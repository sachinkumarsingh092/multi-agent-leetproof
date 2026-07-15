"""Goal parsing and manipulation utilities."""

import logging
import re
from typing import Awaitable, List, Dict, Callable, Tuple, Union, Optional

from utils.lean.types import Goal, LakeBuildResult, LeanDiagnostic, Param
from utils.lean.constants import TURNSTILE
from utils.lean.normalization import normalize_extracted_goal_fields


# Type alias for line predicates: can be a regex pattern string or a callable
LinePredicate = Union[str, Callable[[str], bool]]


def _make_predicate(pred: LinePredicate) -> Callable[[str], bool]:
    """Convert a predicate (string pattern or callable) to a callable."""
    if isinstance(pred, str):
        pattern = re.compile(pred)
        return lambda line: pattern.search(line) is not None
    return pred


def find_lines_matching(code: str, predicate: LinePredicate) -> List[int]:
    """Find line numbers (1-indexed) of all lines matching the predicate.

    Args:
        code: Code string to search
        predicate: Either a regex pattern string, or a callable (str) -> bool

    Returns:
        List of line numbers (1-indexed) where predicate matches, in order.
    """
    pred_fn = _make_predicate(predicate)
    matching_lines = []
    for line_num, line in enumerate(code.splitlines(), start=1):
        if pred_fn(line):
            matching_lines.append(line_num)
    return matching_lines


def find_sorry_lines(code: str) -> List[int]:
    """Find line numbers (1-indexed) of all 'sorry' occurrences in code.

    Args:
        code: Lean code string

    Returns:
        List of line numbers (1-indexed) where 'sorry' appears, in order of occurrence.
    """
    return find_lines_matching(code, r'\bsorry\b')


def extract_try_this_suggestion(diagnostic_message: str) -> Optional[str]:
    try_this = "Try this:"
    if diagnostic_message.startswith(try_this):
        suggestion = diagnostic_message[len(try_this):].strip()
        return suggestion
    return None


def apply_try_this_suggestion(code: str, diag_line: int, diag_column: int, suggestion: str) -> Optional[str]:
    """Replace a '?'-tactic at the diagnostic position with a 'Try this' suggestion.

    Locates the tactic word on the diagnostic line starting at diag_column,
    consuming characters until '?' (inclusive), then substitutes suggestion.

    Returns the modified code, or None if the position is out of bounds.
    """
    lines = code.splitlines()
    idx = diag_line - 1
    if not (0 <= idx < len(lines)):
        return None
    line = lines[idx]
    col = diag_column
    end = col
    while end < len(line) and line[end] != '?':
        end += 1
    end += 1  # include the '?'
    lines[idx] = line[:col] + suggestion + line[end:]
    return "\n".join(lines)


logger = logging.getLogger(__name__)


async def refine_suggestions(
    code: str,
    diagnostics: List[LeanDiagnostic],
    check_build: Callable[[str], Awaitable[LakeBuildResult]],
) -> Tuple[str, LakeBuildResult | None]:
    """Apply all 'Try this' suggestions from diagnostics, typechecking each one.

    Iterates through diagnostics, and for each "Try this" suggestion, applies it
    at the diagnostic position and typechecks. If the build passes, the change is
    kept; otherwise it is skipped.

    Returns:
        Tuple of (refined_code, build_result). If no suggestions were applied
        successfully, refined_code is the original code and build_result is None.
    """
    refined = code
    refined_build: LakeBuildResult | None = None
    for diag in diagnostics:
        suggestion = extract_try_this_suggestion(diag.message)
        if suggestion:
            applied = apply_try_this_suggestion(refined, diag.line, diag.column, suggestion)
            if applied is not None:
                applied_result = await check_build(applied)
                if applied_result.typechecks:
                    refined = applied
                    refined_build = applied_result
                else:
                    logger.warning(
                        f"[refine_suggestions] Suggestion '{suggestion}' didn't typecheck, skipping"
                    )
    return refined, refined_build


def replace_on_lines(
    code: str,
    replacement_map: Dict[int, str],
    pattern: str,
) -> str:
    """Replace pattern matches on specified lines with the corresponding replacement.

    Lines not in the map are unchanged.

    Args:
        code: Original code
        replacement_map: Dict mapping line number (1-indexed) -> replacement string
        pattern: Regex pattern to replace on matching lines

    Returns:
        Code with pattern replaced according to the map.
    """
    compiled_pattern = re.compile(pattern)
    lines = code.splitlines()
    result_lines = []

    for line_num, line in enumerate(lines, start=1):
        if line_num in replacement_map:
            new_line = compiled_pattern.sub(replacement_map[line_num], line)
            result_lines.append(new_line)
        else:
            result_lines.append(line)

    return '\n'.join(result_lines)


def replace_sorries_by_line(code: str, replacement_map: Dict[int, str]) -> str:
    """Replace 'sorry' on specified lines with the corresponding replacement.

    Lines not in the map keep their 'sorry' unchanged.

    Args:
        code: Original code with sorry placeholders
        replacement_map: Dict mapping line number (1-indexed) -> replacement string

    Returns:
        Code with sorries replaced according to the map.
    """
    return replace_on_lines(code, replacement_map, r'\bsorry\b')


def goal_as_sorried(goal: Goal):
    """Get goal as a sorried theorem."""
    return goal.as_sorried()

def exact_goal(goal: Goal) -> str:
    return f"exact {goal_invocation(goal)}"


def goal_invocation(goal: Goal) -> str:
    """Generate deterministic goal invocation syntax for after loom_solve.

    Args:
        goal: Goal object with name and params

    Returns:
        String like "(goal0 param1 param2 ...)" to be added after loom_solve
    """
    param_names = " ".join(param.name for param in goal.params)
    if param_names:
        return f"({goal.name} {param_names})"
    else:
        return f"({goal.name})"


def generate_goal_invocations(goals: List[Goal]) -> str:
    """Generate all goal invocations to add after loom_solve.

    Args:
        goals: List of Goal objects

    Returns:
        String with all goal invocations, one per line, indented
    """
    if not goals:
        return ""
    return "\n".join(f"  {goal_invocation(goal)}" for goal in goals)


def _is_indented(line: str) -> bool:
    """Check if line starts with whitespace."""
    return bool(line) and line[0].isspace()


def _is_param_line(raw_line: str) -> bool:
    """Check if line is a param: not indented and contains ' :'."""
    return not _is_indented(raw_line) and " :" in raw_line


def _is_case_line(line: str) -> bool:
    """Check if line is a case tag marker (e.g., 'case left' or 'case «ensures_1: ...»')."""
    return line.startswith("case ")


def _extract_case_tag(line: str) -> str:
    """Extract the case tag from a case line."""
    return line[5:].strip()  # Remove "case " prefix


def parse_lean_goals(content: str) -> List[Goal]:
    """Parse Lean goals from content.

    Rules:
    - 'case ...' marks a case tag for the next goal
    - '⊢ ...' starts a goal
    - Unindented line with ' :' is a param
    - Indented lines continue the previous item
    """
    params: List[Param] = []
    goals: List[Goal] = []
    lines = content.splitlines()
    idx = 0
    current_case_tag: Optional[str] = None

    def collect_continuations() -> List[str]:
        """Collect indented continuation lines, advance idx."""
        nonlocal idx
        parts = []
        while idx < len(lines):
            raw = lines[idx]
            stripped = raw.strip()
            if not stripped or not _is_indented(raw):
                break
            parts.append(stripped)
            idx += 1
        return parts

    while idx < len(lines):
        raw = lines[idx]
        line = raw.strip()

        if not line:
            idx += 1
            continue

        # Case tag marker
        if _is_case_line(line):
            current_case_tag = _extract_case_tag(line)
            idx += 1
            continue

        # Goal
        if line.startswith(TURNSTILE):
            first_part = line[len(TURNSTILE):].strip()
            idx += 1
            continuations = collect_continuations()
            goal_str = " ".join([first_part] + continuations) if first_part else " ".join(continuations)
            normalized_param_types, goal_str, current_case_tag = normalize_extracted_goal_fields(
                [param.ty for param in params],
                goal_str,
                current_case_tag,
            )
            normalized_params = [
                Param(param.name, normalized_param_types[i])
                for i, param in enumerate(params)
            ]
            goals.append(Goal(f"goal_{len(goals)}", normalized_params, goal_str, current_case_tag))
            params = []
            current_case_tag = None  # Reset case tag after goal is created
            continue

        # Param
        if _is_param_line(raw):
            names_str, type_str = line.split(" :", 1)
            names = names_str.split()
            idx += 1
            continuations = collect_continuations()
            full_type = " ".join([type_str.strip()] + continuations) if type_str.strip() else " ".join(continuations)
            for name in names:
                params.append(Param(name, full_type))
            continue

        if params:
            raise RuntimeError(f"Cannot parse line {idx + 1}: {line}")

        idx += 1

    return goals
