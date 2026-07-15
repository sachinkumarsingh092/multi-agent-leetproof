"""Code transformation utilities for Lean files."""

import re
import textwrap
from typing import Tuple, List

from logging_config import get_logger
from utils.lean.constants import (
    PROVE_CORRECT_PATTERN,
    LOOM_SOLVE_PATTERN,
    COMMENT_PREFIX_PATTERN,
    SUBGOAL_PLACEHOLDER,
)

logger = get_logger(__name__)


def extract_lean_code_from_md_block(llm_output: str) -> str:
    """Extract Lean code from LLM output (handles markdown code blocks).

    Extracts the LAST code block found, which is safer when the LLM
    outputs initial thinking/reasoning and then corrects itself.

    Args:
        llm_output: Raw LLM output text

    Returns:
        Extracted Lean code
    """
    # Try to extract from ```lean code blocks - find ALL matches and take the last
    matches = re.findall(r"```lean\s*\n(.*?)\n```", llm_output, re.DOTALL)
    if matches:
        return matches[-1]  # Return the last match

    # Try generic code block - find ALL matches and take the last
    matches = re.findall(r"```.*?\s*\n(.*?)\n```", llm_output, re.DOTALL)
    if matches:
        return matches[-1]  # Return the last match

    # No code block found, return entire output
    logger.warning("No code block found in LLM output, using entire response")
    return llm_output

def uncomment_lines_matching(
    content: str,
    pattern: str,
    preserve_space_after_comment: bool = True,
) -> Tuple[str, bool]:
    """Uncomment all lines matching a regex pattern.

    Removes '-- ' from lines where the uncommented part matches the pattern.

    Args:
        content: The file content
        pattern: Regex pattern to match against uncommented line content
        preserve_space_after_comment: Whether to preserve space after --

    Returns:
        Tuple of (modified_content, was_modified)
    """
    lines = content.split("\n")
    modified_lines = []
    was_modified = False
    compiled_pattern = re.compile(pattern)

    for line in lines:
        commented_match = re.match(r"^(\s*)(--)(\s*)(.*)$", line)
        if commented_match:
            indent = commented_match.group(1)
            indent_after_comment = (
                commented_match.group(3) if preserve_space_after_comment else ""
            )
            rest = commented_match.group(4)

            if compiled_pattern.match(rest):
                modified_lines.append(f"{indent}{indent_after_comment}{rest}")
                was_modified = True
            else:
                modified_lines.append(line)
        else:
            modified_lines.append(line)

    return ("\n".join(modified_lines), was_modified)


def comment_lines_matching(content: str, pattern: str) -> Tuple[str, bool]:
    """Comment all lines matching a regex pattern.

    Adds '-- ' to lines that match the pattern.

    Args:
        content: The file content
        pattern: Regex pattern to match against line content

    Returns:
        Tuple of (modified_content, was_modified)
    """
    lines = content.split("\n")
    modified_lines = []
    was_modified = False
    compiled_pattern = re.compile(pattern)

    for line in lines:
        commented_match = re.match(r"^(\s*)--", line)
        if not commented_match:
            content_match = re.match(r"^(\s*)(.*)$", line)
            if content_match:
                indent = content_match.group(1)
                rest = content_match.group(2)

                if compiled_pattern.match(rest):
                    modified_lines.append(f"{indent}-- {rest}")
                    was_modified = True
                else:
                    modified_lines.append(line)
            else:
                modified_lines.append(line)
        else:
            modified_lines.append(line)

    return ("\n".join(modified_lines), was_modified)


def extract_and_move_proof_blocks(content: str) -> Tuple[str, List[str]]:
    """Extract commented prove_correct and loom_solve blocks and remove from original content.

    Args:
        content: File content with commented proof blocks

    Returns:
        Tuple of (content_without_blocks, list_of_extracted_blocks)
    """
    lines = content.split("\n")
    extracted_indices = set()
    extracted_blocks = []

    prove_correct_commented = re.compile(COMMENT_PREFIX_PATTERN + PROVE_CORRECT_PATTERN)
    loom_solve_commented = re.compile(COMMENT_PREFIX_PATTERN + LOOM_SOLVE_PATTERN)

    i = 0
    while i < len(lines):
        line = lines[i]

        if prove_correct_commented.search(line):
            block_lines = [line]
            extracted_indices.add(i)
            j = i + 1

            while j < len(lines):
                next_line = lines[j]
                if re.match(r"^\s*--", next_line):
                    block_lines.append(next_line)
                    extracted_indices.add(j)
                    if loom_solve_commented.search(next_line):
                        j += 1
                        break
                    j += 1
                else:
                    break

            extracted_blocks.append("\n".join(block_lines))
            i = j
        else:
            i += 1

    content_without_blocks = "\n".join(
        line for i, line in enumerate(lines) if i not in extracted_indices
    )

    return (content_without_blocks, extracted_blocks)


def add_grind_attributes(content: str, lemma_names: List[str]) -> str:
    """Add grind and solverHint attributes for given lemmas.

    Args:
        content: File content
        lemma_names: List of lemma names to add to grind sets

    Returns:
        Content with attribute declarations appended
    """
    if not lemma_names:
        return content

    lemma_names_str = " ".join(lemma_names)
    attributes_block = f"""
attribute [solverHint] {lemma_names_str}
attribute [grind] {lemma_names_str}
"""
    return content + "\n" + attributes_block


def remove_import_statements(text: str) -> str:
    """Remove import statements from Lean code."""
    return remove_import_lines(text)


def remove_import_lines(text: str) -> str:
    """Remove lines starting with 'import' or 'open'.

    Args:
        text: Lean code text

    Returns:
        Text with import/open lines removed
    """
    lines = text.split("\n")
    filtered_lines = []
    for line in lines:
        stripped = line.strip()
        if not (stripped.startswith("import ") or stripped.startswith("open ")):
            filtered_lines.append(line)
    return "\n".join(filtered_lines)


def filter_map_only_defs_and_theorems(node, proof_placeholder: str = "..."):
    """Filter and map Lean AST nodes to only include definitions and theorems.

    Filters out nodes with "test" prefix and maps theorems/definitions to their
    string representation, replacing theorem proofs with a placeholder.

    Args:
        node: A Lean AST node (LeanTheorem or LeanDef)
        proof_placeholder: The placeholder to use for theorem proofs (default: "...")

    Returns:
        String representation of the node if it's a definition or theorem, None otherwise
    """
    # Lazy import to avoid circular dependency
    from utils.lean_proof_parser import LeanTheorem, LeanDef, LeanProof, LeanTactic

    # Filter out anything with "test" prefix
    # if node.name.startswith("test"):
    #     return None
    if isinstance(node, LeanTheorem):
        node.proof = LeanProof(
            is_by=True, is_inline=True, tactics=[LeanTactic(content=proof_placeholder)]
        )
        return str(node)

    if isinstance(node, LeanDef):
        return str(node)


def mask_lean_comments(text: str) -> str:
    """Replace comments and strings in Lean code with spaces, preserving layout.

    Handles:
    - Nested block comments: /- ... /- ... -/ ... -/
    - Line comments: -- ...
    - Strings: " ... " (with escaped quotes)

    Returns:
        String of same length as input, with non-code characters replaced by spaces.
    """
    chars = list(text)
    n = len(chars)
    i = 0
    nested_comment_level = 0
    in_line_comment = False
    in_string = False

    while i < n:
        if nested_comment_level > 0:
            # Inside block comment
            if text.startswith("-/", i):
                nested_comment_level -= 1
                chars[i] = " "
                chars[i + 1] = " "
                i += 2
            elif text.startswith("/-", i):
                nested_comment_level += 1
                chars[i] = " "
                chars[i + 1] = " "
                i += 2
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
            continue

        if in_line_comment:
            # Inside line comment
            if chars[i] == "\n":
                in_line_comment = False
                i += 1
            else:
                chars[i] = " "
                i += 1
            continue

        if in_string:
            # Inside string
            if chars[i] == "\\":
                # Escape next char
                chars[i] = " "  # Mask escape backslash
                if i + 1 < n:
                    if chars[i + 1] != "\n":
                        chars[i + 1] = " "  # Mask escaped char
                    i += 2
                else:
                    i += 1
            elif chars[i] == '"':
                in_string = False
                chars[i] = " "  # Mask closing quote
                i += 1
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
            continue

        # Outside comments and strings
        if text.startswith("/-", i):
            nested_comment_level += 1
            chars[i] = " "
            chars[i + 1] = " "
            i += 2
        elif text.startswith("--", i):
            in_line_comment = True
            chars[i] = " "
            chars[i + 1] = " "
            i += 2
        elif chars[i] == '"':
            in_string = True
            chars[i] = " "
            i += 1
        else:
            # Normal code, leave as is
            i += 1

    return "".join(chars)


def replace_sorry_with_placeholder(text: str, placeholder: str = SUBGOAL_PLACEHOLDER) -> str:
    """Replace `sorry` with a placeholder tactic, ensuring `by` is present.

    Algorithm:
    - Mask comments and strings to avoid false positives.
    - For each `sorry` in masked text, check term-mode or tactic-mode.
    - Term mode: `sorry` -> `by <placeholder>`
    - Tactic mode: `sorry` -> `<placeholder>`

    Detection:
    - If `:=` immediately precedes `sorry` on the same line -> term mode
    - If `by` precedes `sorry` on same line, or a parent line ends with `by` -> tactic mode
    """
    masked_text = mask_lean_comments(text)
    
    # We work with parallel lists: original lines for output, masked lines for analysis
    lines = text.split('\n')
    masked_lines = masked_text.split('\n')
    result_lines = lines.copy()

    # Simple patterns (applied to masked lines)
    ENDS_WITH_BY = re.compile(r'\bby\s*$')       # line ends with 'by' (word)
    ENDS_WITH_ASSIGN = re.compile(r':=\s*$')     # line ends with ':='

    def get_indent(line: str) -> int:
        return len(line) - len(line.lstrip())

    def is_word_sorry(line: str, idx: int) -> bool:
        """Check if 'sorry' at idx is a standalone word."""
        before_ok = idx == 0 or not (line[idx - 1].isalnum() or line[idx - 1] == '_')
        after_ok = idx + 5 >= len(line) or not (line[idx + 5].isalnum() or line[idx + 5] == '_')
        return before_ok and after_ok

    # Note: is_in_comment is no longer needed because we search in masked_text

    def has_by_binding(masked_lines: list, line_idx: int, sorry_col: int) -> bool:
        """Check if sorry is in tactic mode (bound to a 'by')."""
        line = masked_lines[line_idx]
        sorry_indent = get_indent(line)
        before_sorry = line[:sorry_col]

        # TERM MODE: ':=' immediately before sorry on same line
        if ENDS_WITH_ASSIGN.search(before_sorry):
            return False

        # TACTIC MODE: 'by' on same line before sorry
        if ENDS_WITH_BY.search(before_sorry):
            return True

        # Look backwards for lines ending with ':=' or 'by'
        for j in range(line_idx - 1, -1, -1):
            prev_line = masked_lines[j]
            stripped = prev_line.strip()

            # Skip empty lines (masked comments became empty or whitespace)
            if not stripped:
                continue

            prev_indent = get_indent(prev_line)

            # 'by' always means tactic mode
            if ENDS_WITH_BY.search(prev_line):
                return True

            # ':=' means term mode ONLY if sorry is more indented
            # (i.e., sorry is the term for this assignment)
            if ENDS_WITH_ASSIGN.search(prev_line):
                if sorry_indent > prev_indent:
                    return False  # term mode
                # else: this := is from a sibling/completed statement, continue

        return False

    # Process lines backwards
    for i in range(len(lines) - 1, -1, -1):
        masked_line = masked_lines[i]
        original_line = lines[i]

        # Find all sorry positions in this line (search in MASKED line)
        sorry_positions = []
        pos = 0
        while True:
            idx = masked_line.find('sorry', pos)
            if idx == -1:
                break
            if is_word_sorry(masked_line, idx):
                sorry_positions.append(idx)
            pos = idx + 1

        # Process right to left to preserve indices
        for sorry_idx in reversed(sorry_positions):
            current_line = result_lines[i]

            if has_by_binding(masked_lines, i, sorry_idx):
                # Tactic mode: just replace sorry
                result_lines[i] = current_line[:sorry_idx] + placeholder + current_line[sorry_idx + 5:]
            else:
                # Term mode: add 'by' before placeholder
                result_lines[i] = current_line[:sorry_idx] + f'by {placeholder}' + current_line[sorry_idx + 5:]

    return '\n'.join(result_lines)


def replace_first_sorry_with_multiline_tactic(
    text: str,
    tactic_script: str | list[str],
) -> str:
    """Replace first standalone ``sorry`` with an indentation-safe tactic script.

    ``tactic_script`` may be either a single string or a list of tactic lines.
    All inserted continuation lines use the indentation level of the line that
    originally contained ``sorry``.
    """
    if isinstance(tactic_script, list):
        tactic_lines = [line.strip() for line in tactic_script if line.strip()]
    else:
        tactic_lines = [line.strip() for line in tactic_script.splitlines() if line.strip()]
    assert tactic_lines, "tactic_script must be non-empty"

    lines = text.split("\n")
    for i, line in enumerate(lines):
        if line.lstrip().startswith("--"):
            continue

        match = re.search(r"\bsorry\b", line)
        if not match:
            continue

        indent = line[: len(line) - len(line.lstrip())]
        start, end = match.span()

        first_line = line[:start] + tactic_lines[0] + line[end:]
        continuation = [indent + t for t in tactic_lines[1:]]

        return "\n".join(lines[:i] + [first_line] + continuation + lines[i + 1:])

    return text
