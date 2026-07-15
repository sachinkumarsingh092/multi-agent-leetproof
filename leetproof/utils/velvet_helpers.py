from dataclasses import MISSING, dataclass
import re
from enum import Enum
from pathlib import Path
from typing import List, Tuple, TypedDict, Literal, Callable, TypeVar
from parsy import generate, string, regex, whitespace, any_char

from utils.lean.constants import LOOM_SOLVE_SIMP_ALL, SET_MAX_HEARTBEATS
from utils.lean.parser import VelvetTestCase, LeanFile
from utils.lean.goals import parse_lean_goals
from utils.lean_helpers import Param
from utils.lean.types import LeanDiagnostic, Goal, LakeBuildResult
from utils.lean_proof_parser import LeanDef, LeanProof, LeanTactic, LeanTheorem
from utils.lean.build import get_simplified_goals_after_loom_solve
from agents.agent_state import PBTStatus
from utils.message_helpers import lean_block
from utils.velvet_types import NameInfo, VelvetMethod
from logging_config import get_logger

logger = get_logger(__name__)

# Whitespace pattern that also skips single-line comments (--)
ws_with_comments = regex(r'(\s|--[^\n]*)+')
ws_with_comments_optional = regex(r'(\s|--[^\n]*)*')

A = TypeVar("A")

def _strip_comments(text: str) -> str:
    """Strip single-line comments (--) from text."""
    return re.sub(r'--[^\n]*', '', text)


class FeatureState(str, Enum):
    MISSING = "MISSING"
    COMMENTED = "COMMENTED"
    UNCOMMENTED = "UNCOMMENTED"
    BROKEN = "BROKEN"


@dataclass
class VelvetFileState:
    """State for the Velvet Programmer agent."""
    method_name: str
    pbt_state: Tuple[FeatureState, str]
    prove_correct_block_state: Tuple[FeatureState, str]
    test_cases_cnt: int

COMMENT = '--'
PROVE_CORRECT = 'prove_correct'
LOOM_SOLVE = 'loom_solve'
EXTRACT_PROGRAM_FOR = 'extract_program_for'
DERIVE_TESTER_FOR = 'derive_tester_for'
PRECOND_DECIDABLE = 'prove_precondition_decidable_for'
POSTCOND_DECIDABLE = 'prove_postcondition_decidable_for'
RUN_ELAB = 'run_elab do'
METHOD_NAME_RE = re.compile(r'\s*\bmethod\s*((\w(\w|\'))*)?.*')
TEST_CASE_RE = re.compile(r'#eval.*run\b')
IDENTIFIER = regex(r"(\w(\w|\')*)")


def get_velvet_file_state(file_content: str) -> VelvetFileState :
    lines = file_content.splitlines()
    prove_correct_block_state: Tuple[FeatureState,str] =  (FeatureState.MISSING,'`prove_correct <MethodName> by\n\tloom_solve` block is missing')
    pbt_state :Tuple[FeatureState,str]=  ( FeatureState.MISSING, f"PBT for the method is missing, cannot find {DERIVE_TESTER_FOR} in the body" )
    method_name =  ''
    test_cases_cnt =  0
    i = 0
    while i < len(lines):
        line = lines[i]
        match = METHOD_NAME_RE.match(line)
        if match:
            method_name = match.group(1).strip()
        if PROVE_CORRECT in line:
            if LOOM_SOLVE in line:
                prove_correct_block_state = (FeatureState.COMMENTED if '--' in line else FeatureState.UNCOMMENTED,'')
            elif i+1 < len(lines) and LOOM_SOLVE in lines[i+1]:
                prove_correct_block_state = (FeatureState.COMMENTED if '--' in line else FeatureState.UNCOMMENTED,'')
            else:
                prove_correct_block_state = (FeatureState.BROKEN, 'prove_correct block seems to be ill-formed or not following the instruction')
        if TEST_CASE_RE.match(line):
            test_cases_cnt += 1
        
        if DERIVE_TESTER_FOR in line:
            pbt_state = (FeatureState.COMMENTED if '--' in line else FeatureState.UNCOMMENTED,'')
            fully_formed = POSTCOND_DECIDABLE in file_content and PRECOND_DECIDABLE in file_content and RUN_ELAB in file_content
            if not fully_formed:
                pbt_state = (FeatureState.BROKEN, '')
            else:
                pbt_state = (FeatureState.MISSING, f"PBT seems to be ill-formed, doesn't have all the required elements [{DERIVE_TESTER_FOR,PRECOND_DECIDABLE, POSTCOND_DECIDABLE, EXTRACT_PROGRAM_FOR, RUN_ELAB}]")
        i += 1
    
    return VelvetFileState(method_name,pbt_state,prove_correct_block_state,test_cases_cnt)


@generate
def _parse_name_info():
    yield whitespace.optional()
    yield string('(')
    yield whitespace.optional()
    has_mut: bool = ( yield string('mut').optional() ) != None
    yield (whitespace if has_mut else whitespace.optional())
    identifier: str = yield IDENTIFIER
    yield whitespace.optional()
    yield string(':')
    yield whitespace.optional()

    cnt = 1
    chars = []
    while cnt != 0:
        char = yield any_char
        chars.append(char)
        if char == '(':
            cnt += 1
        if char == ')':
            cnt -= 1
    chars.pop()
    ty = ''.join(chars).strip()

    return NameInfo(identifier,ty,has_mut)

def _parse_body_by_indentation(text: str) -> str | None:
    """Parse method body based on indentation.

    Takes text starting after 'do', captures lines that maintain
    at least the indentation level of the first non-empty line.
    Stops on dedent.
    """
    lines = text.split('\n')
    body_indent = None
    body_lines = []

    for line in lines:
        # Skip empty lines before we find body indent
        if body_indent is None:
            if line.strip() == '':
                body_lines.append(line)
                continue
            # First non-empty line sets the indentation level
            body_indent = len(line) - len(line.lstrip())
            body_lines.append(line)
        else:
            # Empty lines are always included
            if line.strip() == '':
                body_lines.append(line)
                continue
            # Check indentation
            current_indent = len(line) - len(line.lstrip())
            if current_indent >= body_indent:
                body_lines.append(line)
            else:
                # Dedent - stop parsing
                break

    body = '\n'.join(body_lines).strip()
    return body if body else None


@generate
def _parse_velvet_method() :
    from parsy import regex, index
    method = regex(r"\bmethod\b")
    returns = regex(r"\breturn\b")
    require = regex(r"\brequire\b")
    ensure = regex(r"\bensures\b")
    do = regex(r"\bdo\b")
    yield ws_with_comments_optional
    yield method
    yield ws_with_comments
    name : str= yield IDENTIFIER
    yield ws_with_comments_optional

    params = []
    param = yield _parse_name_info.optional()
    while param:
        params.append(param)
        param = yield _parse_name_info.optional()
    yield ws_with_comments
    yield returns
    yield ws_with_comments
    # parse until require or ensures
    retval = yield _parse_name_info
    yield ws_with_comments
    if (yield require.optional()) == None:
        # We didn't find require
        yield ensure
        chars = yield any_char.until(do)
        # may have multiple ensures
        ensure_clauses = list(map( lambda s : s.strip() ,''.join(chars).strip().split('ensures')))
        # Consume 'do' and capture body
        yield do
        remaining = yield regex(r'[\s\S]*')  # Capture everything remaining
        body = _parse_body_by_indentation(remaining)
        return VelvetMethod(name,params,retval,[],ensure_clauses,body)
    else:
        chars = yield any_char.until(ensure)
        requires = list(map(lambda s : s.strip() ,''.join(chars).strip().split('require')))
        yield ensure
        chars = yield any_char.until(do)
        # may have multiple ensures
        ensure_clauses = list(map( lambda s : s.strip() ,''.join(chars).strip().split('ensures')))
        # Consume 'do' and capture body
        yield do
        remaining = yield regex(r'[\s\S]*')  # Capture everything remaining
        body = _parse_body_by_indentation(remaining)
        return VelvetMethod(name,params,retval,requires,ensure_clauses,body)

def get_velvet_method(content: str) -> VelvetMethod :
    # Strip comments before parsing to avoid matching keywords inside comments
    content = _strip_comments(content)
    lines = content.splitlines()
    method_at = 0
    for i, line in enumerate(lines):
        if line.startswith("method "):
            method_at = i
            
    rest = "\n".join(lines[method_at:])

    return _parse_velvet_method.parse_partial(rest)[0]

def get_pbt_code_snippet(velvet_method: VelvetMethod, max_ms: int = 5000) -> str:
    return f"velvet_plausible_test {velvet_method.name} (config := {{ maxMs := some {max_ms} }})"


def is_pbt_counterexample(diagnostic: LeanDiagnostic) -> bool:
    """Check if a diagnostic is a PBT counterexample.

    Args:
        diagnostic: The LeanDiagnostic to check

    Returns:
        True if this is a PBT counterexample message
    """
    return '[velvet_plausible_test] FAIL:' in diagnostic.message


def get_pbt_counterexamples(diagnostics: List[LeanDiagnostic]) -> List[LeanDiagnostic]:
    """Filter diagnostics to get only PBT counterexamples.

    Args:
        diagnostics: List of LeanDiagnostic objects

    Returns:
        List of diagnostics that are PBT counterexamples
    """
    return [d for d in diagnostics if is_pbt_counterexample(d)]


def format_pbt_feedback(counterexamples: List[LeanDiagnostic]) -> str:
    """Format PBT counterexamples as feedback for the LLM.

    Args:
        counterexamples: List of LeanDiagnostic counterexample messages

    Returns:
        Formatted feedback string
    """
    if not counterexamples:
        return ""

    header = (
        "PROPERTY-BASED TESTING FOUND FAILURES\n"
        "======================================\n"
        "The current implementation has issues - PBT found inputs that violate the specification.\n"
        "This could be a failed invariant, postcondition, or decreasing check.\n"
    )

    examples = []
    for ce in counterexamples:
        examples.append(f"  - {ce.message}")

    footer = "\nPlease fix the implementation to handle these cases correctly."

    return f"{header}\n" + '\n'.join(examples) + f"\n{footer}"



def run_two_phase_pbt(
    output_file: str,
    build_pbt_content: Callable[[int], str],
    *,
    compile_failure_comment: str,
    log_prefix: str = "PBT",
    phase_budgets_ms: Tuple[int, int] = (5000, 20000),
) -> tuple[PBTStatus, LakeBuildResult | None, dict | None]:
    """Run the shared two-phase PBT flow used by Velvet and Lean wrappers."""
    from tools.common import lean_build_file_helper

    try:
        pbt_result = None

        for phase_idx, max_ms in enumerate(phase_budgets_ms):
            pbt_content = build_pbt_content(max_ms)
            lean_file = LeanFile.from_path(output_file)
            lean_file.add_or_replace_section("Pbt", pbt_content, after="Assertions")
            lean_file.reconstruct_and_write_to_file(Path(output_file))
            logger.info(f"Added {log_prefix} section ({max_ms}ms)")

            pbt_result = lean_build_file_helper(output_file, context_lines=0, include_info_logs=True)
            if not pbt_result.typechecks:
                logger.warning(f"{log_prefix} section caused build failure, commenting it out")
                lean_file = LeanFile.from_path(output_file)
                lean_file.comment_out_section("Pbt", compile_failure_comment)
                lean_file.reconstruct_and_write_to_file(Path(output_file))
                logger.info("Commented out PBT section")
                return (PBTStatus.ADDED_COMPILE_FAILED, pbt_result, None)

            counterexamples = get_pbt_counterexamples(pbt_result.diagnostics)
            if counterexamples:
                feedback = format_pbt_feedback(counterexamples)
                logger.warning(f"{log_prefix} ({max_ms}ms) found {len(counterexamples)} failure(s)")
                return (
                    PBTStatus.ADDED_AND_PASSED,
                    pbt_result,
                    {"typechecks": False, "build_log": feedback},
                )

            if phase_idx + 1 < len(phase_budgets_ms):
                logger.info(
                    f"{log_prefix} ({max_ms}ms) passed, running extended check with {phase_budgets_ms[phase_idx + 1]}ms"
                )

        logger.info(f"{log_prefix} passed all checks; keeping PBT section enabled")
        return (PBTStatus.ADDED_AND_PASSED, pbt_result, None)

    except Exception as e:
        logger.warning(f"Could not add {log_prefix} section: {e}")
        return (PBTStatus.NOT_ADDED, None, None)


def generate_assertions(method: VelvetMethod, test_cases: List[VelvetTestCase]) -> str:
    """Generate the content for an Assertions section.

    Args:
        method: The VelvetMethod being tested
        test_cases: List of VelvetTestCase objects

    Returns:
        The content for the Assertions section (without section/end markers)
    """
    snippets = []
    for test_case in test_cases:
        snippet = construct_assertion_snippet_v2(method, test_case)
        snippets.append(f"-- Test case {test_case.id}")
        snippets.append(snippet)
        snippets.append("")  # blank line between test cases

    return '\n'.join(snippets).strip()


def construct_assertion_snippet(method: VelvetMethod, test_case: VelvetTestCase) -> str:
    """Construct a #guard_msgs assertion snippet for a test case.

    For non-mutable methods:
        #eval (MethodName test1_a test1_b).run
        returns: DivM.res <inlined_return_value>

    For mutable methods:
        #eval (MethodName test1_arr).run
        returns: DivM.res (<inlined_return>, <inlined_mut1_final>, ...)

    Args:
        method: The VelvetMethod being tested
        test_case: The VelvetTestCase with inputs and expected outputs

    Returns:
        A string containing the #guard_msgs assertion code
    """
    test_name = test_case.name  # e.g., "test1"

    # Build the method call arguments using def names (test1_a, test1_b, etc.)
    args = []
    for param in method.params:
        if param.name in test_case.inputs:
            args.append(f"{test_name}_{param.name}")

    # Build the expected result with inlined values
    mutable_params = [p for p in method.params if p.is_mut]

    if mutable_params:
        # For mutable params: DivM.res (<return>, <mut1_final>, <mut2_final>, ...)
        result_parts = []

        # Return value (inlined)
        if test_case.expected_return:
            result_parts.append(test_case.expected_return)

        # Mutated param values (inlined, in order of params)
        for param in mutable_params:
            if param.name in test_case.expected_mutations:
                result_parts.append(test_case.expected_mutations[param.name])

        expected = f"({', '.join(result_parts)})"
    else:
        # For non-mutable: DivM.res <return> (inlined)
        expected = test_case.expected_return or "()"

    # Construct the snippet
    snippet = f"""/--
info: DivM.res {expected}
-/
#guard_msgs in
#eval ({method.name} {' '.join(args)}).run"""

    return snippet

def construct_assertion_snippet_v2(method: VelvetMethod, test_case: VelvetTestCase) -> str:
    """Construct a #guard_msgs assertion snippet for a test case.

    For non-mutable methods:
        #assert_same_evaluation #[MethodName test1_a test1_b).run, DivM.res (<ret>)]

    For mutable methods:
        #assert_same_evaluation #[(MethodName test1_arr).run , DivM.res(<ret>,<mut1_final>, <mut2_final>)]

    Args:
        method: The VelvetMethod being tested
        test_case: The VelvetTestCase with inputs and expected outputs

    Returns:
        A string containing the #guard_msgs assertion code
    """
    test_name = test_case.name  # e.g., "test1"

    # Build the method call arguments using def names (test1_a, test1_b, etc.)
    args = []
    for param in method.params:
        if param.name in test_case.inputs:
            args.append(f"{test_name}_{param.name}")

    mutable_params = [p for p in method.params if p.is_mut]

    if mutable_params:
        # For mutable params: DivM.res (<return>, <mut1_final>, <mut2_final>, ...)
        result_parts = []

        if test_case.expected_return:
            result_parts.append(f"{test_case.name}_Expected")

        # Mutated param values 
        for param in mutable_params:
            if param.name in test_case.expected_mutations:
                result_parts.append( f"{test_case.name}_Expected_{param.name}")

        expected = f"({', '.join(result_parts)})"
    else:
        # For non-mutable: DivM.res <return> (reference)
        expected = f"{test_case.name}_Expected"

    # Construct the snippet
    snippet = f"""
#assert_same_evaluation #[(({method.name} {' '.join(args)}).run), DivM.res {expected} ]"""

    return snippet

def get_prove_correct_block(method: VelvetMethod):
    return f"""
prove_correct {method.name} by
{indent(LOOM_SOLVE_SIMP_ALL, 2)}
"""


HINTS_BEGIN_MARKER = "-- HINTS BEGIN"
HINTS_END_MARKER = "-- HINTS END"
HINTS_BLOCK_RE = re.compile(
    rf"{re.escape(HINTS_BEGIN_MARKER)}[\s\S]*?{re.escape(HINTS_END_MARKER)}\n?"
)
AUTO_GRIND_HINTS_ENABLED = False


def build_grind_attributes_block(lemma_names: list[str]) -> str:
    """Build attribute block for grind declarations.

    Returns empty string when there are no valid names.
    """
    if not AUTO_GRIND_HINTS_ENABLED:
        return ""

    names = sorted({name.strip() for name in lemma_names if name and name.strip()})
    if not names:
        return ""
    names_str = " ".join(names)
    return f"attribute [grind] {names_str}"


def build_hints_block(lemma_names: list[str]) -> str:
    """Build a marked hints block for section Proof."""
    attrs = build_grind_attributes_block(lemma_names)
    if not attrs:
        return ""
    return f"{HINTS_BEGIN_MARKER}\n{attrs}\n{HINTS_END_MARKER}"


def upsert_hints_block(section_content: str, lemma_names: list[str]) -> str:
    """Upsert/remove marked hints block in section content.

    - If a marked block exists, replace it with hints derived from lemma_names.
    - If no marked block exists, append hints to the end when non-empty.
    - If lemma_names is empty, remove the marked block when present.
    """
    hints_block = build_hints_block(lemma_names)
    content = section_content or ""
    if HINTS_BLOCK_RE.search(content):
        if hints_block:
            updated = HINTS_BLOCK_RE.sub(hints_block + "\n", content, count=1)
        else:
            updated = HINTS_BLOCK_RE.sub("", content, count=1)
        return updated.strip()

    if not hints_block:
        return content

    base = content.rstrip()
    if not base:
        return hints_block
    return f"{base}\n\n{hints_block}"


def indent(content: str, by: int):
    return (" " * by) + content


def normalize_body_with_while_tags(body: str) -> str:
    """Normalize a Velvet method body by tagging statements with their while context.

    - Statements outside while loops: kept as-is
    - While loops: become <whileN> tags
    - Statements inside while loops: prefixed with <whileN>:
    - Nested whiles: <while1>:<while2>:
    - Annotations (invariant, done_with, decreasing) between while and do: stripped

    Example:
        let mut i := 0
        while i < 10
            invariant i >= 0
        do
            i := i + 1
        return i

    Becomes:
        let mut i := 0
        <while1>
            <while1>:i := i + 1
        return i
    """
    if not body:
        return ""

    lines = body.split('\n')
    result: List[str] = []
    i = [0]  # Use list for mutability in nested function
    while_counter = [0]

    def process_block(base_indent: int, tag_prefix: str) -> None:
        while i[0] < len(lines):
            line = lines[i[0]]
            stripped = line.strip()

            if not stripped:
                result.append("")
                i[0] += 1
                continue

            current_indent = len(line) - len(line.lstrip())
            if current_indent < base_indent:
                break

            if stripped.startswith('while '):
                while_counter[0] += 1
                my_tag = f"<while{while_counter[0]}>"
                full_tag = f"{tag_prefix}{my_tag}" if tag_prefix else my_tag
                result.append(' ' * current_indent + full_tag)

                # Check if 'do' is on the same line as 'while'
                if stripped.endswith(' do'):
                    i[0] += 1
                else:
                    i[0] += 1
                    # Skip annotations until 'do'
                    while i[0] < len(lines):
                        s = lines[i[0]].strip()
                        if s == 'do' or s.endswith(' do'):
                            i[0] += 1
                            break
                        i[0] += 1

                # Process while body with tag prefix
                process_block(current_indent + 1, full_tag + ":")
            else:
                # Regular statement
                if tag_prefix:
                    result.append(' ' * current_indent + tag_prefix + stripped)
                else:
                    result.append(line)
                i[0] += 1

    process_block(0, "")
    return '\n'.join(result)


def make_remove_sections_preprocess(*section_names: str) -> Callable[[LeanFile], LeanFile]:
    """Return a goal-extraction preprocess that removes the given sections."""
    sections = tuple(section_names)

    def preprocess(lean_file: LeanFile) -> LeanFile:
        present_sections = [name for name in sections if lean_file.get_section(name) is not None]
        if not present_sections:
            return lean_file

        preprocessed = LeanFile.from_content(lean_file.reconstruct())
        for name in present_sections:
            preprocessed.remove_section(name)
        return preprocessed

    return preprocess


GOAL_EXTRACTION_NOISE_SECTIONS = ("Pbt", "TestCases", "Assertions")
remove_goal_extraction_noise = make_remove_sections_preprocess(
    *GOAL_EXTRACTION_NOISE_SECTIONS
)
remove_pbt_section = make_remove_sections_preprocess("Pbt")


def identity(value: A) -> A:
    """Return the value unchanged."""
    return value


DEFAULT_GRIND_GEN_PARAM_RETRY_ORDER = (4, 2, 1)


@dataclass(frozen=True)
class GoalExtractionResult:
    """Result of extracting goals after a temporary `loom_solve` proof."""

    goal_result_str: str
    cleaned_content: str
    grind_gen_param: int | None
    goals: list[Goal]


class GoalExtractionError(RuntimeError):
    """Base error for loom goal extraction failures."""


class GoalExtractionTimeoutError(GoalExtractionError):
    """Raised when goal extraction still times out after retries."""


class GoalExtractionDiagnosticError(GoalExtractionError):
    """Raised when extraction yields diagnostics but no parseable goals."""


def build_custom_loom_solver_prelude(gen_param: int) -> str:
    """Build a custom `loom_solver` tactic override for goal extraction retries."""
    return (
        'set_option loom.solver "custom"\n\n'
        "macro_rules\n"
        "| `(tactic|loom_solver) => `(tactic|(\n"
        "  try injections\n"
        "  try subst_vars\n"
        f"  try grind (gen := {gen_param})))"
    )


def is_goal_extraction_timeout(goal_result_str: str) -> bool:
    """Return whether the raw extraction diagnostic indicates a timeout."""
    return "build timed out" in goal_result_str.lower()


async def extract_goals_after_loom_solve(
    program: str,
    output_file: str,
    *,
    preprocess: Callable[[LeanFile], LeanFile],
    postprocess: Callable[[LeanFile], LeanFile],
    section_name: str = "Proof",
    cleanup_mode: Literal["remove", "clear", "comment_out"] = "remove",
    hints_lemmas: list[str] | None = None,
    proof_prelude: str = "",
) -> tuple[str, str]:
    """Extract unprovable goals using a temporary loom_solve Proof section.

    The helper temporarily injects a section (default: `Proof`) with
    `loom_solve`, extracts goals from build diagnostics, then cleans up the
    temporary proof snippet.

    `preprocess` is applied only to the temporary extraction view that is
    written to disk right before running `loom_solve` goal extraction.
    `postprocess` runs later on the cleaned original `LeanFile`, after the
    temporary proof snippet has been removed/cleared/commented out. It does
    not receive the preprocessed extraction view.

    Cleanup behavior is controlled by ``cleanup_mode``:
    - ``"remove"``: remove the section entirely (historical behavior)
    - ``"clear"``: keep `section <name> ... end <name>` but clear its content
    - ``"comment_out"``: keep the section and comment out injected proof lines

    Args:
        program: The Lean program content
        output_file: Path to write and build
        preprocess: Transform the temporary extraction view before writing it
            to disk for `loom_solve` goal extraction.
        postprocess: Transform the cleaned original file after cleanup. This
            runs on `lean_file`, not on the preprocessed extraction view.
        section_name: Section used to inject temporary proof snippet
        cleanup_mode: How to clean up temporary proof content
        hints_lemmas: Optional lemma names to inject as a marked hints block
            (`-- HINTS BEGIN` ... `-- HINTS END`) in the temporary Proof section
        proof_prelude: Optional prelude inserted into the temporary proof
            section before `prove_correct` (e.g. solver overrides/macros).

    Returns:
        Tuple of (goal_result_string, cleaned_program_content)
    """
    lean_file = LeanFile.from_content(program)
    impl = lean_file.get_section("Impl", assert_exists=True).content
    method = get_velvet_method(impl)
    path = Path(output_file)

    hints_block = build_hints_block(hints_lemmas or [])
    prove_block = get_prove_correct_block(method).strip()

    # Inject temporary proof snippet for goal extraction.
    proof_parts = [SET_MAX_HEARTBEATS]
    if proof_prelude.strip():
        proof_parts.append(proof_prelude.strip())
    if hints_block:
        proof_parts.append(hints_block)
    proof_parts.append(prove_block)

    lean_file.add_or_replace_section(
        section_name,
        "\n\n".join(proof_parts)
    )
    extraction_view = preprocess(lean_file)
    extraction_view.reconstruct_and_write_to_file(path)

    goal_result_str = get_simplified_goals_after_loom_solve(str(path))

    # Cleanup temporary proof snippet according to the requested mode.
    if cleanup_mode == "remove":
        lean_file.remove_section(section_name)
    elif cleanup_mode == "clear":
        if hints_block:
            # Keep persistent hints in Proof section for downstream proving.
            lean_file.add_or_replace_section(section_name, hints_block)
        else:
            lean_file.clear_section(section_name)
    elif cleanup_mode == "comment_out":
        lean_file.comment_out_section(
            section_name,
            reason=f"Temporary goal extraction proof in section '{section_name}' (commented out)",
        )
    else:
        raise ValueError(f"Unknown cleanup_mode: {cleanup_mode}")

    lean_file = postprocess(lean_file)

    cleaned_content = lean_file.reconstruct_and_write_to_file(path)

    return goal_result_str, cleaned_content


async def extract_goals_after_loom_solve_with_retry(
    program: str,
    output_file: str,
    *,
    preprocess: Callable[[LeanFile], LeanFile],
    postprocess: Callable[[LeanFile], LeanFile],
    section_name: str = "Proof",
    cleanup_mode: Literal["remove", "clear", "comment_out"] = "remove",
    hints_lemmas: list[str] | None = None,
    preferred_grind_gen_param: int | None = None,
) -> GoalExtractionResult:
    """Extract goals, retrying on timeout with a custom `loom_solver`."""

    def classify_and_parse_goal_extraction_result(
        result: GoalExtractionResult,
    ) -> GoalExtractionResult:
        if is_goal_extraction_timeout(result.goal_result_str):
            raise GoalExtractionTimeoutError(result.goal_result_str.strip())

        goals = parse_lean_goals(result.goal_result_str)
        if result.goal_result_str.strip() and not goals:
            raise GoalExtractionDiagnosticError(
                "Goal extraction failed: Lean returned an error diagnostic, "
                "but no parseable goals were produced.\n"
                f"Raw diagnostic:\n{result.goal_result_str.strip()}"
            )

        return GoalExtractionResult(
            goal_result_str=result.goal_result_str,
            cleaned_content=result.cleaned_content,
            grind_gen_param=result.grind_gen_param,
            goals=goals,
        )

    async def extract_raw_result_after_loom_solve(
        gen_param: int | None,
    ) -> GoalExtractionResult:
        proof_prelude = (
            build_custom_loom_solver_prelude(gen_param)
            if gen_param is not None
            else ""
        )
        goal_result_str, cleaned_content = await extract_goals_after_loom_solve(
            program,
            output_file,
            preprocess=preprocess,
            postprocess=postprocess,
            section_name=section_name,
            cleanup_mode=cleanup_mode,
            hints_lemmas=hints_lemmas,
            proof_prelude=proof_prelude,
        )
        return GoalExtractionResult(
            goal_result_str=goal_result_str,
            cleaned_content=cleaned_content,
            grind_gen_param=gen_param,
            goals=[],
        )

    if preferred_grind_gen_param is not None:
        logger.info(
            "Goal extraction using preferred custom loom solver (gen := %s)",
            preferred_grind_gen_param,
        )
        return classify_and_parse_goal_extraction_result(
            await extract_raw_result_after_loom_solve(preferred_grind_gen_param)
        )

    result = await extract_raw_result_after_loom_solve(None)
    if not is_goal_extraction_timeout(result.goal_result_str):
        return classify_and_parse_goal_extraction_result(result)

    last_result = result
    for gen_param in DEFAULT_GRIND_GEN_PARAM_RETRY_ORDER:
        logger.warning(
            "Goal extraction timed out; retrying with custom loom solver (gen := %s)",
            gen_param,
        )
        last_result = await extract_raw_result_after_loom_solve(gen_param)
        if not is_goal_extraction_timeout(last_result.goal_result_str):
            return classify_and_parse_goal_extraction_result(last_result)

    raise GoalExtractionTimeoutError(last_result.goal_result_str.strip())


def goal_target_starts_with_wpgen(goal: Goal) -> bool:
    """Check whether a goal target starts with WPGen."""
    return goal.final_goal.lstrip().startswith("WPGen")


def find_wpgen_goals(goals: list[Goal]) -> list[Goal]:
    """Filter goals whose target starts with WPGen."""
    return [goal for goal in goals if goal_target_starts_with_wpgen(goal)]


def extract_wpgen_target_from_diagnostic(diagnostic_message: str) -> str | None:
    """Best-effort extraction of a WPGen target from raw diagnostics.

    Some loom failures report as:
      "Failed to prove assertion without names: WPGen ..."
    instead of pretty goal blocks parseable by parse_lean_goals.
    """
    msg = diagnostic_message.strip()

    prefix = "Failed to prove assertion without names:"
    if msg.startswith(prefix):
        rest = msg[len(prefix):].lstrip()
        if rest.startswith("WPGen"):
            return rest.splitlines()[0].strip()

    for line in msg.splitlines():
        stripped = line.strip()
        if stripped.startswith("⊢"):
            target = stripped.lstrip("⊢").strip()
            if target.startswith("WPGen"):
                return target

    return None


# --- Invariant goal extraction and formatting utilities ---

@dataclass
class InvariantGoal:
    """Represents an unprovable goal related to a specific invariant."""
    invariant_name: str
    invariant_statement: str  # The original invariant as written
    goal: "Goal"

    def summary(self) -> str:
        goal_str = self.goal.final_goal[:150]
        if len(self.goal.final_goal) > 150:
            goal_str += "..."
        return f"[{self.invariant_name}] {goal_str}"


@dataclass
class NonInvariantGoal:
    """Represents a goal that uses invariants in premises but is not an invariant goal itself.

    These are typically postcondition/ensures goals that depend on the invariants.
    If these are unprovable, it indicates the invariants may need strengthening.
    """
    goal_type: str  # e.g., "ensures", "postcondition", "other"
    goal: "Goal"

    def summary(self) -> str:
        return f"[{self.goal_type}]\n{self.goal.as_theorem()}"


def _parse_invariant_case_tag(case_tag: str | None) -> tuple[str | None, str | None]:
    """Parse invariant name and statement from a case tag.

    Case tags look like: «invariant_dp_bound: ∀ k, k < dp.size → dp[k]! ≤ m»
    """
    if not case_tag:
        return None, None

    if case_tag.startswith('ensures_'):
        return None, None

    clean_tag = case_tag.strip('«»')
    match = re.match(r'invariant_([^:]+):\s*(.+)', clean_tag)
    if match:
        return match.group(1).strip(), match.group(2).strip()

    return None, None


def _parse_non_invariant_goal_type(case_tag: str | None) -> str | None:
    """Parse goal type from a non-invariant case tag.

    Returns the goal type (e.g., "ensures", "postcondition") or None if it's an invariant goal.
    """
    if not case_tag:
        return "other"

    clean_tag = case_tag.strip('«»')

    # Check if this is an invariant goal - if so, return None
    if re.match(r'invariant_([^:]+):\s*(.+)', clean_tag):
        return None

    # Check for ensures goals
    if clean_tag.startswith('ensures_'):
        return "ensures"

    # For any other case tag, return it as the type
    return clean_tag if clean_tag else "other"


def partition_invariant_goals(
    goals: list[Goal],
) -> tuple[list[InvariantGoal], list[NonInvariantGoal]]:
    """Partition parsed goals into invariant and non-invariant categories."""
    inv_goals = []
    non_inv_goals = []

    for goal in goals:
        name, statement = _parse_invariant_case_tag(goal.case_tag)
        if name:
            inv_goals.append(InvariantGoal(
                invariant_name=name,
                invariant_statement=statement or "",
                goal=goal,
            ))
        else:
            goal_type = _parse_non_invariant_goal_type(goal.case_tag)
            non_inv_goals.append(NonInvariantGoal(
                goal_type=goal_type or "other",
                goal=goal,
            ))

    return inv_goals, non_inv_goals


def extract_invariant_goals(
    diagnostic_message: str,
) -> tuple[list[InvariantGoal], list[NonInvariantGoal]]:
    """Extract and partition goals into invariant and non-invariant categories.

    Returns:
        A tuple of (invariant_goals, non_invariant_goals) where:
        - invariant_goals: Goals directly about proving invariants
        - non_invariant_goals: Goals that use invariants in premises (e.g., ensures goals)
    """
    goals = parse_lean_goals(diagnostic_message)
    return partition_invariant_goals(goals)


def get_context_for_correctness_check(goal: InvariantGoal, spec: str, impl: str) -> str:
    """Get context for the correctness checker LLM."""
    return f"""## Invariant `{goal.invariant_name}`

**Original statement:** `{goal.invariant_statement}`

### Specification
{lean_block(spec)}

### Implementation
{lean_block(impl)}"""


def format_correctness_feedback(
    inv_goal: InvariantGoal,
    is_provable: bool,
    justification: str,
    correction_hint: str,
) -> str:
    """Format feedback from the correctness checker."""
    status = "Provable" if is_provable else "UNPROVABLE"

    feedback = f"""### Invariant `{inv_goal.invariant_name}` - {status}

**Original Invariant:** `{inv_goal.invariant_statement}`
"""

    if justification:
        feedback += f"\n**Why It Fails:** {justification}\n"

    if correction_hint:
        feedback += f"\n**Suggested Direction:** {correction_hint}\n"

    feedback += (
        "\n**Verification Condition Generated for This Invariant:**\n"
        f"{lean_block(inv_goal.goal.as_theorem())}\n"
    )

    return feedback


def get_context_for_invariant_strength_check(
    goal: NonInvariantGoal, spec: str, impl: str
) -> str:
    """Get context for checking if invariants are strong enough for a non-invariant goal."""
    return f"""## Goal Type: `{goal.goal_type}`

### Specification
{lean_block(spec)}

### Implementation
{lean_block(impl)}"""


def format_invariant_strength_feedback(
    goal: NonInvariantGoal,
    is_provable: bool,
    justification: str,
    strengthening_hint: str,
) -> str:
    """Format feedback for invariant strength check on non-invariant goals."""
    status = "Provable" if is_provable else "UNPROVABLE (invariants may need strengthening)"

    feedback = f"""### {goal.goal_type.capitalize()} Goal - {status}
"""

    if justification:
        feedback += f"\n**Why Current Invariants Are Insufficient:** {justification}\n"

    if strengthening_hint:
        feedback += f"\n**Suggested Invariant Strengthening:** {strengthening_hint}\n"

    feedback += (
        "\n**Verification Condition That Still Needs To Be Proved:**\n"
        f"{lean_block(goal.goal.as_theorem())}\n"
    )

    return feedback
