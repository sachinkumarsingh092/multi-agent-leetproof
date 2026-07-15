"""Reusable automation functions for goal discharge and plausibility checking.

Extracted from VelvetInvariantInferrerAgent and ProverAgent so that any agent
can use these mechanical operations without tight coupling.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable

from config.timeouts import Timeouts
from logging_config import get_logger
from tools.pantograph_client import PantographClient
from tools.proof_search import (
    ProofSearcher,
    ValidatedTacticProofStatus,
    WeightedTactic,
)
from utils.lean.types import LakeBuildResult
from utils.proof_types import AutomationResult

logger = get_logger(__name__)


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------

@dataclass
class DischargeResult:
    """Result of batch goal discharge."""
    discharged: list[Any] = field(default_factory=list)
    undischarged: list[Any] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Automation tactics
# ---------------------------------------------------------------------------

async def try_automation_tactics(
    client: PantographClient,
    sorried_theorem: str,
    tactics: list[str],
) -> AutomationResult:
    """Try automation tactics via Pantograph's try_all_tactics.

    Args:
        client: PantographClient with environment loaded.
        sorried_theorem: Theorem text with exactly one sorry.
        tactics: Tactic list to try.

    Returns:
        AutomationResult with success, applied_tactic, proof, build_result.
    """
    tactic_result = await client.try_all_tactics(sorried_theorem, tactics)
    return AutomationResult(
        success=tactic_result.success,
        applied_tactic=tactic_result.tactic,
        proof=tactic_result.proof,
        build_result=tactic_result.build_result,
    )


# ---------------------------------------------------------------------------
# Goal discharge
# ---------------------------------------------------------------------------

async def try_discharge_goal(
    client: PantographClient,
    tactic_pool: list[WeightedTactic],
    goal,
    automation_tactics: list[str],
    *,
    max_search_steps: int = 200,
    proof_search_enabled: bool = False
) -> bool:
    """Try to discharge a goal using automation tactics and MCTS proof search.

    Step 1: Try automation tactics (via try_automation_tactics).
    Step 2: If step 1 fails, run MCTS proof search with the tactic pool.

    Args:
        client: PantographClient with specs loaded.
        tactic_pool: Weighted tactics for MCTS proof search.
        goal: Goal to discharge (must have .as_sorried() method).
        automation_tactics: Tactic list to try before MCTS.
        max_search_steps: Max MCTS steps. Defaults to 200.

    Returns:
        True if the goal was discharged, False otherwise.
    """
    sorried = goal.as_sorried()

    # Step 1: try automation tactics
    try:
        result = await try_automation_tactics(client, sorried, automation_tactics)
        if result.success:
            return True
    except Exception as e:
        logger.warning(f"try_all_tactics failed for {goal.name}: {e}")

    if not proof_search_enabled:
        logger.info(f"Proof search is disabled")
        return False

    # Step 2: MCTS proof search (+ tactic recovery/check_build validation)
    try:
        searcher = ProofSearcher(client, tactic_pool=tactic_pool)
        validated = await searcher.search_validated_tactic_proof(
            goal,
            max_steps=max_search_steps,
            max_duration_seconds=Timeouts.PROOF_SEARCH,
        )

        if validated.status == ValidatedTacticProofStatus.SEARCH_FAILED:
            return False

        # Mechanical discharge only needs a solved search state, but log
        # recovery/validation issues for debugging and hardening.
        if validated.tactic_proof is not None:
            logger.info("Recovered theorem for %s:\n%s", goal.name, validated.tactic_proof.rstrip())

        if validated.status == ValidatedTacticProofStatus.RECOVERY_FAILED:
            logger.warning(
                "Proof search solved %s but tactic recovery failed",
                goal.name,
            )
        elif validated.status == ValidatedTacticProofStatus.BUILD_FAILED:
            logger.warning(
                "Proof search solved %s but recovered tactic proof failed check_build",
                goal.name,
            )
        return True
    except Exception as e:
        logger.warning(f"Proof search failed for {goal.name}: {e}")
        return False


def _default_goal_accessor(wrapper: Any):
    return wrapper.goal


def _default_label_accessor(wrapper: Any) -> str:
    return (
        getattr(wrapper, 'invariant_name', None)
        or getattr(wrapper, 'goal_type', None)
        or getattr(wrapper.goal, 'name', '?')
    )


async def discharge_goals(
    client: PantographClient,
    tactic_pool: list[WeightedTactic],
    goals: list[Any],
    automation_tactics: list[str],
    *,
    goal_accessor: Callable[[Any], Any] | None = None,
    label_accessor: Callable[[Any], str] | None = None,
    max_search_steps: int = 200,
    enable_proof_search: bool = False,
) -> DischargeResult:
    """Try to discharge goals via automation + MCTS.

    Args:
        client: PantographClient with specs loaded.
        tactic_pool: Weighted tactics for MCTS proof search.
        goals: List of goal wrappers to try discharging.
        automation_tactics: Tactic list to try before MCTS.
        goal_accessor: Extract the Goal from a wrapper. Defaults to lambda g: g.goal.
        label_accessor: Extract a label for logging.
        max_search_steps: Max MCTS steps per goal.

    Returns:
        DischargeResult with discharged and undischarged lists.
    """
    get_goal = goal_accessor or _default_goal_accessor
    get_label = label_accessor or _default_label_accessor

    discharged: list[Any] = []
    undischarged: list[Any] = []

    for i, goal_wrapper in enumerate(goals):
        goal = get_goal(goal_wrapper)
        label = get_label(goal_wrapper)
        logger.info(f"[{i+1}/{len(goals)}] Trying to discharge '{label}':\n{goal.as_sorried()}")
        try:
            success = await try_discharge_goal(
                client, tactic_pool, goal,
                automation_tactics=automation_tactics,
                max_search_steps=max_search_steps,
                proof_search_enabled=enable_proof_search
            )
        except Exception as e:
            logger.warning(f"Discharge failed for goal {goal.name}, falling back to LLM for rest: {e}")
            undischarged.append(goal_wrapper)
            undischarged.extend(goals[i + 1:])
            break
        if success:
            logger.info(f"Goal '{label}' discharged mechanically")
            discharged.append(goal_wrapper)
        else:
            undischarged.append(goal_wrapper)

    logger.info(f"Mechanical discharge: {len(discharged)}/{len(goals)} discharged")
    return DischargeResult(discharged=discharged, undischarged=undischarged)


# ---------------------------------------------------------------------------
# Plausibility checking
# ---------------------------------------------------------------------------

async def try_plausible(
    client: PantographClient,
    goal,
) -> tuple[bool, LakeBuildResult]:
    """Run plausible' to check if a goal has a counter-example.

    Replaces sorry with '(try aesop); plausible'' and checks build output
    for "Found a counter-example" message.

    Args:
        client: PantographClient with specs loaded.
        goal: Goal to check (must have .as_sorried() and .name).

    Returns:
        Tuple of (has_counter_example, build_result).
    """
    sorried = goal.as_sorried()
    candidate = sorried.replace("sorry", "(try aesop) <;> plausible'", 1)
    result = await client.check_build(candidate, include_info_logs=True)
    all_messages = " ".join(d.message for d in result.diagnostics)
    has_counter_example = "Found a counter-example" in all_messages
    if has_counter_example:
        logger.warning(f"Counter-example found for {goal.name}")
    return has_counter_example, result
