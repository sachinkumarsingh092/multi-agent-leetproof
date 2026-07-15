"""Utilities for removing unused variables from proved theorems and managing proof sections.

Includes both:
- Build-time removal: strips unused params based on ``lake build`` diagnostics.
- Runtime filtering: uses Pantograph's ``clear`` and ``revert`` tactics to find
  which context variables are actually essential for a goal.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Set, List, Callable, Optional, TYPE_CHECKING

from utils.lean.types import Goal, LeanDiagnostic
from utils.lean.parser import LeanFile
from logging_config import get_logger

if TYPE_CHECKING:
    from pantograph.expr import GoalState

logger = get_logger(__name__)

UNUSED_VAR_PATTERN = re.compile(r"unused variable `([^`]+)`")


# =============================================================================
# Pure functions (easily testable)
# =============================================================================

def extract_unused_vars(
    diagnostics: List[LeanDiagnostic],
    line_filter: Callable[[int], bool] = lambda _: True,
) -> Set[str]:
    """Extract unused variable names from warning diagnostics."""
    unused = set()
    for diag in diagnostics:
        if diag.severity == "warning" and line_filter(diag.line):
            match = UNUSED_VAR_PATTERN.search(diag.message)
            if match:
                unused.add(match.group(1))
    return unused


def get_proof_body(theorem_content: str) -> str:
    """Extract the proof body (everything after ':= by')."""
    match = re.search(r':=\s*by\b', theorem_content)
    if not match:
        return ""
    return theorem_content[match.end():]


def get_vars_referenced_in_proof(theorem_content: str) -> Set[str]:
    """Get variable names that appear in the proof body.

    This is used to prevent removing params that are referenced in the proof,
    even if Lean reports them as 'unused' (e.g., params that are only used in 'clear').
    """
    proof_body = get_proof_body(theorem_content)
    if not proof_body:
        return set()
    # Match identifiers (simple heuristic)
    identifiers = set(re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_\']*)\b', proof_body))
    return identifiers


def filter_goal_params(goal: Goal, unused_vars: Set[str]) -> Goal:
    """Create a new Goal with unused params removed."""
    if not unused_vars:
        return goal

    filtered_params = [p for p in goal.params if p.name not in unused_vars]

    if len(filtered_params) == len(goal.params):
        return goal

    removed = [p.name for p in goal.params if p.name in unused_vars]
    logger.info(f"Filtered {len(removed)} unused param(s) from {goal.name}: {removed}")

    return Goal(
        name=goal.name,
        params=filtered_params,
        final_goal=goal.final_goal,
        case_tag=goal.case_tag,
    )


def replace_theorem_signature(theorem_content: str, filtered_goal: Goal) -> str:
    """Replace theorem signature while keeping proof body intact.

    Only handles tactic mode proofs (`:= by ...`). Term mode proofs are not supported.
    """
    # Find ':=' followed by whitespace/newline and 'by' to avoid matching
    # ':=' inside let expressions in the type signature
    match = re.search(r':=\s*by\b', theorem_content)
    if not match:
        raise ValueError(f"Could not find ':= by' in theorem: {theorem_content[:100]}...")

    proof_part = theorem_content[match.start():]
    new_signature = filtered_goal.as_theorem()

    return f"{new_signature} {proof_part}"


def temp_section_name_for_goal(goal_name: str) -> str:
    """Generate temp section name for a goal."""
    return f"Proof_{goal_name}"


# =============================================================================
# Section finalization functions
# =============================================================================

@dataclass
class UnusedVarRemovalResult:
    """Result of removing unused variables from a theorem."""
    goal: Goal
    theorem: str
    changed: bool


def remove_unused_vars(
    goal: Goal,
    theorem_content: str,
    diagnostics: List[LeanDiagnostic],
) -> UnusedVarRemovalResult:
    """Remove unused variables from a proved theorem.

    Pure function: no file I/O, no section management.
    Diagnostics should be scoped to the theorem content (line numbers relative to it).
    """
    unused_vars = extract_unused_vars(diagnostics)

    if not unused_vars:
        logger.info(f"No unused variables found for {goal.name}")
        return UnusedVarRemovalResult(goal=goal, theorem=theorem_content, changed=False)

    # Don't remove vars that are referenced in the proof body (e.g., in 'clear' statements)
    vars_in_proof = get_vars_referenced_in_proof(theorem_content)
    vars_to_keep = unused_vars & vars_in_proof
    if vars_to_keep:
        logger.info(f"Keeping {len(vars_to_keep)} var(s) referenced in proof body: {vars_to_keep}")
        unused_vars -= vars_to_keep

    if not unused_vars:
        logger.info(f"No variables to remove after filtering out proof-body references")
        return UnusedVarRemovalResult(goal=goal, theorem=theorem_content, changed=False)

    logger.info(f"Removing {len(unused_vars)} unused variable(s) from {goal.name}: {unused_vars}")

    filtered_goal = filter_goal_params(goal, unused_vars)
    cleaned_theorem = replace_theorem_signature(theorem_content, filtered_goal)

    logger.info(f"Cleaned theorem for {goal.name}:\n{cleaned_theorem}")

    return UnusedVarRemovalResult(goal=filtered_goal, theorem=cleaned_theorem, changed=True)


# =============================================================================
# Runtime essential-variable detection (Pantograph-based)
# =============================================================================

async def find_essential_vars(
    goal_state: "GoalState",
    server,
) -> Set[str]:
    """Find essential context variables for a goal using Pantograph tactics.

    Returns the set of variable names that should be kept — both variables
    that the goal target directly needs AND hypotheses that say something
    about those variables (transitively).

    **Phase 1 — iterative** ``clear``:

    ``clear x`` in Lean removes ``x`` from the context.  It *fails* if
    ``x`` appears in the goal target or in some other hypothesis's type.
    We repeatedly try ``clear v`` for every variable; successes update the
    state so that previously-blocked clears may now succeed.  Once nothing
    more can be cleared, whatever remains = variables the goal target
    directly needs.  That is the *base* essential set.

    Example — ``Context: n : Nat, k : Nat, z : Nat``  Goal: ``n + k = k + n``::

        clear z  → succeeds  (z not in goal, nothing depends on z)
        clear n  → fails     (n in goal target)
        clear k  → fails     (k in goal target)
        ⇒ essential = {n, k}

    **Phase 2 — dependency expansion via** ``revert``:

    Phase 1 may discard useful hypotheses.  For instance if the context
    has ``hx : x > 0`` and the goal mentions ``x`` but not ``hx``,
    Phase 1 clears ``hx``.  Phase 2 brings it back because ``hx``'s type
    references the essential variable ``x``.

    We use Lean's ``revert`` tactic: ``revert x`` moves ``x`` into the
    goal target *and also reverts every hypothesis whose type mentions*
    ``x``.  By comparing which variables disappear we detect type-level
    dependencies without any string/regex parsing.

    Two sub-passes per round, repeated to a fixed point:

    *Forward pass* — for each essential ``x``, ``revert x`` on the
    **original** state.  Any non-essential variable that disappears has a
    type mentioning ``x`` → promote it.

    Example::

        Context: v : Nat, x : Nat, hx : x > 0, z : v + x = 0
        Goal: x = x
        Phase 1 essential = {x}          (hx, z, v all cleared)

        Forward: revert x  →  also reverts hx, z (their types mention x)
                 promote hx, z  →  essential = {x, hx, z}

    *Backward pass* — for each non-essential ``v``, ``revert v`` on the
    original state.  If an essential variable is *also* reverted, that
    essential variable's type mentions ``v`` → so ``v`` is needed.

    This catches the *reverse* direction: an essential var's type
    depending on a non-essential var.

    Continuing the example::

        essential = {x, hx, z}   (z : v + x = 0 was promoted)
        non_essential = {v}

        Backward: revert v  →  also reverts z (z's type mentions v)
                  z ∈ essential  →  promote v
                  essential = {x, hx, z, v}

    Without the backward pass, ``v`` would be lost even though the
    essential hypothesis ``z : v + x = 0`` references it.  This matters
    when the utility is used for variable removal (the theorem would not
    typecheck without ``v``), and for proof search it ensures we generate
    tactics for all relevant variables (e.g. ``generalizing v``).
    """
    from pantograph.expr import Site
    from pantograph.server import ServerError, TacticFailure

    if not goal_state.goals:
        return set()

    goal = goal_state.goals[0]
    all_var_names = {v.name for v in goal.variables if v.name}

    if not all_var_names:
        return set()

    # ------------------------------------------------------------------
    # Phase 1: Iterative clearing
    # ------------------------------------------------------------------
    state = goal_state
    while True:
        remaining = [v.name for v in state.goals[0].variables if v.name]
        cleared_any = False
        for name in remaining:
            try:
                state = await server.goal_tactic_async(
                    state, f"clear {name}", site=Site(goal_id=0),
                )
                cleared_any = True
            except (TacticFailure, ServerError):
                pass
        if not cleared_any:
            break

    essential = {v.name for v in state.goals[0].variables if v.name}
    non_essential = all_var_names - essential

    if not non_essential:
        logger.info(f"find_essential_vars: all variables essential: {essential}")
        return essential

    logger.info(
        f"find_essential_vars phase 1: essential={essential}, "
        f"non_essential={non_essential}"
    )

    # ------------------------------------------------------------------
    # Phase 2: Expand via revert (dependency detection)
    # ------------------------------------------------------------------
    changed = True
    while changed:
        changed = False

        # Forward: revert each essential var on the ORIGINAL state.
        # ``revert x`` also reverts every variable whose type mentions x.
        for x in list(essential):
            try:
                new_state = await server.goal_tactic_async(
                    goal_state, f"revert {x}", site=Site(goal_id=0),
                )
                remaining = {
                    v.name for v in new_state.goals[0].variables if v.name
                }
                reverted = all_var_names - remaining
                for v in reverted:
                    if v in non_essential:
                        essential.add(v)
                        non_essential.discard(v)
                        changed = True
            except (TacticFailure, ServerError):
                pass

        # Backward: revert each non-essential var; if doing so also
        # reverts an essential var, the non-essential one is needed
        # (the essential variable's type references it).
        for v in list(non_essential):
            try:
                new_state = await server.goal_tactic_async(
                    goal_state, f"revert {v}", site=Site(goal_id=0),
                )
                remaining = {
                    vv.name for vv in new_state.goals[0].variables if vv.name
                }
                reverted = all_var_names - remaining
                if reverted & essential:
                    essential.add(v)
                    non_essential.discard(v)
                    changed = True
            except (TacticFailure, ServerError):
                pass

    logger.info(f"find_essential_vars phase 2: final essential={essential}")
    logger.info(f"Non essential vars: {non_essential}")
    return essential


async def minimize_goal(
    goal: Goal,
    goal_state: "GoalState",
    server,
) -> Goal:
    """Return a copy of *goal* with only essential params kept.

    Combines :func:`find_essential_vars` (Pantograph-based detection) with
    :func:`filter_goal_params` (param filtering) into a single call.

    Logs a before/after diff of the theorem signature so reviewers can
    see exactly which params were dropped.
    """
    essential = await find_essential_vars(goal_state, server)
    non_essential = {p.name for p in goal.params} - essential

    if not non_essential:
        logger.info(f"minimize_goal({goal.name}): no params to remove")
        return goal

    minimized = filter_goal_params(goal, non_essential)

    # Log the transformation
    removed = sorted(non_essential)
    logger.info(
        f"minimize_goal({goal.name}): removed {len(removed)} param(s): {removed}\n"
        f"  before: {goal.as_theorem()}\n"
        f"   after: {minimized.as_theorem()}"
    )

    return minimized
