"""Lean code processing utilities.

This package provides utilities for working with Lean 4 code:
- types: Core data types (Param, Goal, LeanDiagnostic, LakeBuildResult)
- constants: Shared constants and patterns
- goals: Goal parsing and manipulation
- transform: Code transformation utilities
- build: Build and diagnostics utilities
- parser: Theorem and file structure parsing utilities
"""

# Types
from utils.lean.types import (
    Param,
    Goal,
    LeanDiagnostic,
    LakeBuildResult,
)

# Constants
from utils.lean.constants import (
    PROVE_CORRECT_PATTERN,
    LOOM_SOLVE_PATTERN,
    LOOM_SOLVE,
    LOOM_SOLVE_SIMP_ALL,
    COMMENT_PREFIX_PATTERN,
    TURNSTILE,
    PARAMS_REGEX,
    SUBGOAL_PLACEHOLDER,
)

# Goals
from utils.lean.goals import (
    goal_as_sorried,
    goal_invocation,
    generate_goal_invocations,
    parse_lean_goals,
)

# Transform
from utils.lean.transform import (
    extract_lean_code_from_md_block,
    uncomment_lines_matching,
    comment_lines_matching,
    extract_and_move_proof_blocks,
    add_grind_attributes,
    remove_import_statements,
    remove_import_lines,
    replace_sorry_with_placeholder,
)

# Build
from utils.lean.build import (
    find_project_root,
    get_simplified_goals_after_loom_solve,
    get_goals_after_loom_solve,
    get_diagnostics,
    parse_lake_build_output,
    _extract_items_from_diagnostics,
    _add_context_to_diagnostic,
)

# Parser
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
    # Section parsing
    Section,
    LeanFile,
    parse_lean_file_sections,
    # Test case parsing
    VelvetTestCase,
    parse_test_cases,
)


__all__ = [
    # Types
    "Param",
    "Goal",
    "LeanDiagnostic",
    "LakeBuildResult",
    # Constants
    "PROVE_CORRECT_PATTERN",
    "LOOM_SOLVE_PATTERN",
    "LOOM_SOLVE",
    "LOOM_SOLVE_SIMP_ALL",
    "COMMENT_PREFIX_PATTERN",
    "TURNSTILE",
    "PARAMS_REGEX",
    "SUBGOAL_PLACEHOLDER",
    "replace_sorry_with_placeholder",
    # Goals
    "goal_as_sorried",
    "goal_invocation",
    "generate_goal_invocations",
    "parse_lean_goals",
    # Transform
    "extract_lean_code_from_md_block",
    "uncomment_lines_matching",
    "comment_lines_matching",
    "extract_and_move_proof_blocks",
    "add_grind_attributes",
    "remove_import_statements",
    "remove_import_lines",
    # Build
    "find_project_root",
    "get_simplified_goals_after_loom_solve",
    "get_goals_after_loom_solve",
    "get_diagnostics",
    "parse_lake_build_output",
    "_extract_items_from_diagnostics",
    "_add_context_to_diagnostic",
    # Parser
    "extract_theorem_name",
    "replace_have_proofs_with_sorry",
    "extract_theorem_signature",
    "normalize_signature",
    "check_theorem_signature_match",
    "parse_theorem",
    "_parse_have_statement",
    "_split_at_first_assignment",
    "_remove_comments",
    "_skip_to_matching_paren",
    "_manual_parse_param",
    "_remove_all_nontheorem_lines",
    # Sections
    "Section",
    "LeanFile",
    "parse_lean_file_sections",
    # Test cases
    "VelvetTestCase",
    "parse_test_cases",
]
