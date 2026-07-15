"""Helper functions for working with Lean code.

This module re-exports everything from utils.lean for backward compatibility.
New code should import directly from utils.lean.
"""

# Re-export everything from the lean subpackage for backward compatibility
from utils.lean import *

# Explicitly re-export for type checkers and IDE support
from utils.lean.types import (
    Param,
    Goal,
    LeanDiagnostic,
    LakeBuildResult,
)

from utils.lean.constants import (
    PROVE_CORRECT_PATTERN,
    LOOM_SOLVE_PATTERN,
    LOOM_SOLVE,
    LOOM_SOLVE_SIMP_ALL,
    COMMENT_PREFIX_PATTERN,
    TURNSTILE,
    PARAMS_REGEX,
)

from utils.lean.goals import (
    goal_as_sorried,
    goal_invocation,
    generate_goal_invocations,
    parse_lean_goals,
)

from utils.lean.transform import (
    extract_lean_code_from_md_block,
    uncomment_lines_matching,
    comment_lines_matching,
    extract_and_move_proof_blocks,
    add_grind_attributes,
    remove_import_statements,
    remove_import_lines,
    filter_map_only_defs_and_theorems,
)

from utils.lean.build import (
    get_simplified_goals_after_loom_solve,
    get_goals_after_loom_solve,
    get_diagnostics,
    parse_lake_build_output,
    _extract_items_from_diagnostics,
    _add_context_to_diagnostic,
)

from utils.lean.parser import (
    extract_theorem_name,
    replace_have_proofs_with_sorry,
    extract_theorem_signature,
    normalize_signature,
    check_theorem_signature_match,
    parse_theorem,
    _parse_have_statement,
    _split_at_first_assignment,
    _remove_comments,
    _skip_to_matching_paren,
    _manual_parse_param,
    _remove_all_nontheorem_lines,
    LeanFile,
    VelvetTestCase,
)

from utils.lean_proof_parser import (
    extract_declarations,
    LeanDef,
    LeanBinder,
    parse_lean_theorem,
)

from typing import Optional, List


# --- Spec Parsing ---

def get_def_by_name(content: str, name: str) -> Optional[LeanDef]:
    """Get a definition by name from Lean content using extract_declarations."""
    decls = extract_declarations(content)
    for decl in decls:
        if isinstance(decl, LeanDef) and decl.name == name:
            return decl
    return None


def parse_def_params(def_content: str) -> List[Param]:
    """Parse parameters from a definition using parse_lean_theorem.

    Given content like 'def precondition (a : Array Int) (b : Int) : Prop := ...'
    Returns list of Param objects for the parameters.
    """
    try:
        parsed = parse_lean_theorem(def_content)
        params = []
        for binder in parsed.params:
            for name in binder.names:
                params.append(Param(name=name, ty=binder.type_expr))
        return params
    except Exception:
        return []


# --- Assertion Generation ---

def generate_lean_assertions(func_name: str, params: List[tuple], test_cases: List[VelvetTestCase]) -> str:
    """Generate assertions for pure Lean functions.

    For pure Lean (no DivM monad), assertions are simpler:
    #assert_same_evaluation #[(funcName arg1 arg2), expected]

    Args:
        func_name: Name of the function
        params: List of (name, type) tuples for function parameters
        test_cases: List of VelvetTestCase objects

    Returns:
        The content for the Assertions section
    """
    snippets = []
    param_names = [p[0] for p in params]

    for test_case in test_cases:
        snippet = construct_lean_assertion_snippet(func_name, param_names, test_case)
        snippets.append(f"-- Test case {test_case.id}")
        snippets.append(snippet)
        snippets.append("")  # blank line between test cases

    return '\n'.join(snippets).strip()


def construct_lean_assertion_snippet(func_name: str, param_names: List[str], test_case: VelvetTestCase) -> str:
    """Construct an assertion snippet for a pure Lean function test case.

    For pure Lean:
        #assert_same_evaluation #[(funcName test1_a test1_b), test1_Expected]
    """
    test_name = test_case.name

    args = []
    for param_name in param_names:
        if param_name in test_case.inputs:
            args.append(f"{test_name}_{param_name}")

    expected = f"{test_name}_Expected"
    return f"#assert_same_evaluation #[({func_name} {' '.join(args)}), {expected}]"


# --- Lean -> Velvet PBT Wrapper Generation ---


def tuple_projection_expr(base_expr: str, tuple_arity: int, index: int) -> str:
    """Project the ``index``-th value from a right-associated Lean tuple expression.

    Lean parses ``A × B × C`` as ``A × (B × C)``. This helper reconstructs the
    projection path needed to recover each logical result component.

    Examples:
        tuple_projection_expr("result", 1, 0) -> "result"
        tuple_projection_expr("result", 2, 0) -> "result.1"
        tuple_projection_expr("result", 2, 1) -> "result.2"
        tuple_projection_expr("result", 3, 1) -> "result.2.1"
    """
    if tuple_arity <= 0:
        raise ValueError(f"tuple_arity must be positive, got {tuple_arity}")
    if index < 0 or index >= tuple_arity:
        raise IndexError(f"index {index} out of bounds for tuple arity {tuple_arity}")

    if tuple_arity == 1:
        return base_expr
    if index == 0:
        return f"{base_expr}.1"
    if tuple_arity == 2 and index == 1:
        return f"{base_expr}.2"
    return tuple_projection_expr(f"{base_expr}.2", tuple_arity - 1, index - 1)



def build_postcondition_application(
    precond_params: List[Param],
    result_params: List[Param],
    result_expr: str = "result",
) -> str:
    """Build a postcondition application for a Lean-synthesized implementation.

    When there are multiple logical result params, Lean synthesis collapses them
    into a single tuple-typed return value. Velvet wrappers must expand that
    tuple back into the original postcondition arity using tuple projections.
    """
    if not result_params:
        raise ValueError("result_params must contain at least one output parameter")

    arg_exprs = [p.name for p in precond_params]
    if len(result_params) == 1:
        arg_exprs.append(result_expr)
    else:
        arg_exprs.extend(
            tuple_projection_expr(result_expr, len(result_params), i)
            for i in range(len(result_params))
        )

    return f"postcondition {' '.join(arg_exprs)}" if arg_exprs else "postcondition"



def build_lean_impl_pbt_section(
    precond_params: List[Param],
    result_params: List[Param],
    *,
    has_precondition: bool,
    impl_name: str = "implementation",
    wrapper_name: str = "implementationPbt",
    max_ms: int = 5000,
) -> str:
    """Build a Velvet wrapper method plus PBT command for a pure Lean impl."""
    if not result_params:
        raise ValueError("result_params must contain at least one output parameter")

    params_str = " ".join(f"({p.name} : {p.ty})" for p in precond_params)
    return_ty = " × ".join(p.ty for p in result_params)
    param_names = " ".join(p.name for p in precond_params)
    impl_call = f"({impl_name} {param_names})" if param_names else impl_name
    postcondition_app = build_postcondition_application(
        precond_params,
        result_params,
        result_expr="result",
    )

    lines = [f"method {wrapper_name}{(' ' + params_str) if params_str else ''}"]
    lines.append(f"  return (result : {return_ty})")
    if has_precondition:
        precondition_app = f"precondition {param_names}" if param_names else "precondition"
        lines.append(f"  require {precondition_app}")
    lines.append(f"  ensures {postcondition_app}")
    lines.append("  do")
    lines.append(f"  return {impl_call}")
    lines.append("")
    lines.append(f"velvet_plausible_test {wrapper_name} (config := {{ maxMs := some {max_ms} }})")

    return "\n".join(lines)


# --- Correctness Theorem Construction ---

def construct_correctness_goal(
    impl_name: str,
    precond_params: List[Param],
    postcond_params: List[Param],
    has_precondition: bool,
) -> Goal:
    """Construct a Goal object for proving implementation correctness.

    The theorem structure is:
        theorem correctness_goal
            (params...)
            (h_precond : precondition params)  -- if precondition exists
            : postcondition params (implementation params) := by
            sorry
    """
    goal_params = precond_params.copy()
    param_names = " ".join(p.name for p in goal_params)

    if has_precondition:
        # Add precondition hypothesis parameter
        precond_param_names = " ".join(p.name for p in precond_params)
        precond_param = Param(
            name="h_precond",
            ty=f"precondition {precond_param_names}" if precond_param_names else "precondition"
        )
        goal_params.append(precond_param)

    impl_call = f"({impl_name} {param_names})" if param_names else f"({impl_name})"
    final_goal = f"postcondition {param_names} {impl_call}" if param_names else f"postcondition {impl_call}"

    return Goal(
        name="correctness_goal",
        params=goal_params,
        final_goal=final_goal
    )
