"""Constants for Lean code processing."""

import re

# Pantograph session imports
VELVET_IMPORTS = [
    "Velvet.Std",
    "Extensions.Tactics",
    "Extensions.SpecDSL",
    "Mathlib.Tactic",
]

SPEC_VALIDATE_IMPORTS = [
    "Init",
    "Mathlib.Tactic",
]

LEAN_SYNTH_IMPORTS = [
    "Init",
    "Mathlib.Tactic",
]

PANTOGRAPH_OPTIONS = {
    "printSorryGoals": True,
    "printDependentMVars": True,
    "printExprAst": True,
}

MAX_HEARTBEATS = 10_000_000
SET_MAX_HEARTBEATS = f"set_option maxHeartbeats {MAX_HEARTBEATS}"
PANTOGRAPH_MAX_HEARTBEATS = f"maxHeartbeats={MAX_HEARTBEATS}"
SET_PP_COERCIONS = "set_option pp.coercions false"
SET_LOOM_TERMINATION_PARTIAL = 'set_option loom.semantics.termination "partial"'
SET_LOOM_TERMINATION_TOTAL = 'set_option loom.semantics.termination "total"'
SET_LOOM_CHOICE_DEMONIC = 'set_option loom.semantics.choice "demonic"'
PANTOGRAPH_PP_COERCIONS = "pp.coercions=false"
PANTOGRAPH_CORE_OPTIONS = [
    PANTOGRAPH_MAX_HEARTBEATS,
    PANTOGRAPH_PP_COERCIONS,
]

# Common regex patterns for Lean proof blocks
PROVE_CORRECT_PATTERN = r'prove_correct\s+\w+\s+by'
LOOM_SOLVE_PATTERN = r'loom_solve'
LOOM_SOLVE = 'loom_solve'
# Historical name kept for compatibility with existing imports/call sites. The
# cleanup tactic intentionally avoids `simp at *`, which can unfold specs into
# extraction-unfriendly goals/hypotheses. The conv => congr <;> simp will
# simplify the goal if it has any {x:=y} thingyss.
# Example (postcondition str.toList { data := outArr_1.toList }.toList) => (postcondition str.data outArr_1.toList)
# simp [-postcondition] at * will basically do simp at *, but will not simplify the postcondition anywhere.
# We observed cases where a single final `expose_names` did not clean things up, while adding
# `expose_names` immediately after this simp step seemed to fix the extracted goals.
LOOM_EXTRACTION_CLEANUP = 'try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names'
LOOM_SOLVE_SIMP_ALL = f'loom_solve <;> ({LOOM_EXTRACTION_CLEANUP})'

# Tactic that tries to solve trivial goals and exposes non-trivial ones via `done` failure
SUBGOAL_PLACEHOLDER = 'try (simp at *); try expose_names; try exact?; done'

# Lean comment pattern (with optional leading whitespace)
COMMENT_PREFIX_PATTERN = r'\s*--\s*'

TURNSTILE = "⊢ "

# Match single-line parameter: "name1 name2 : type"
PARAMS_REGEX = re.compile(r"([^:]+) : (.+)")

# Match multi-line parameter start: "name1 name2 :" (colon at end, type on next lines)
PARAMS_MULTILINE_START_REGEX = re.compile(r"([^:]+) :$")

AUTOMATION = [
    "intros; expose_names; try simp_all; try grind",
    "intros; expose_names; try ( simp at * ); try grind",
    "intros; expose_names; grind",
    "intros; expose_names; rfl",
    "intros; expose_names; assumption",
    "intros; expose_names; exact?",
    "intros; expose_names; decide",
]

VELVET_AUTOMATION = AUTOMATION + [
    "intros; expose_names; loom_auto",
]
