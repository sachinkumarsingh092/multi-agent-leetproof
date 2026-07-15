"""Velvet Proof Orchestrator Agent - Orchestrates proof generation and final assembly."""

from typing import Optional, TYPE_CHECKING, Protocol
from pathlib import Path
import re

from dbos import DBOS
from langgraph.graph import StateGraph, START, END

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel

from agents.agent_state import VelvetAgentState, GoalStatus, GoalState
from agents.base import BaseAgent
from tools.common import lean_build_file_helper
from utils.lean.goals import exact_goal
from utils.lean.parser import LeanFile
from utils.validation import validate_output_file
from utils.lean_helpers import LOOM_SOLVE_SIMP_ALL
from logging_config import get_logger
from utils.velvet_helpers import (
    SET_MAX_HEARTBEATS,
    build_custom_loom_solver_prelude,
    get_prove_correct_block,
    get_velvet_method,
    indent,
    extract_goals_after_loom_solve_with_retry,
    remove_goal_extraction_noise,
)
from utils.proof_types import ProofResult, ProvingContext
from utils.lean.build import find_project_root
from utils.lean.constants import (
    PANTOGRAPH_CORE_OPTIONS,
    PANTOGRAPH_OPTIONS,
    VELVET_IMPORTS,
)
from tools.pantograph_client import PantographClient, PantographFactory
from utils.program_state import ProgramBuffer
from utils.shutdown import shutdown_boundary, shutdown_hook, ShutdownHookMode

logger = get_logger(__name__)


class GoalProver(Protocol):
    """Minimal prover interface needed by the proof orchestrator."""

    async def prove(
        self,
        ctx: ProvingContext,
        max_depth: int = 4,
    ) -> ProofResult: ...

    def write_shutdown_snapshot(
        self,
        ctx: ProvingContext,
        *,
        extra_lemma_blocks: list[str] | None = None,
    ) -> str: ...


@DBOS.dbos_class()
class VelvetProofOrchestratorAgent(BaseAgent):
    """Agent that orchestrates proof generation via recursive decomposition.

    This agent:
    1. Routes goals to the ProverAgent for recursive decomposition proving
    2. Tracks goal status (UNPROCESSED -> PROVEN/FAILED)
    3. Performs final assembly: moves proof blocks, adds goal applications
    4. Typechecks the final result
    """

    name = "velvet_proof_orchestrator"
    description = "Orchestrates proof generation and final assembly"
    system_prompt: str = ""  # Not used - this agent orchestrates, doesn't use LLM directly

    def __init__(
        self,
        config: "LLMConfig",
        *,
        prover: GoalProver,
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self.prover = prover
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    @staticmethod
    def _get_goal_by_status(goals: list, status: GoalStatus) -> tuple[int, dict | None]:
        """Get the first goal with the given status."""
        for i, goal in enumerate(goals):
            if goal["status"] == status:
                return i, goal
        return -1, None

    @staticmethod
    def _update_goal(goals: list, goal_idx: int, **updates) -> list:
        """Create a copy of goals list with updates applied to goal at goal_idx.

        Automatically serializes Goal objects to dicts for DBOS persistence.
        """
        from utils.lean.types import Goal

        # Serialize Goal objects in updates
        serialized_updates = {}
        for key, value in updates.items():
            if key == "goal" and isinstance(value, Goal):
                serialized_updates[key] = value.to_dict()
            elif key == "proof_result" and value is not None and hasattr(value, "to_dict"):
                serialized_updates[key] = value.to_dict()
            else:
                serialized_updates[key] = value

        updated_goals = goals.copy()
        updated_goals[goal_idx] = {**goals[goal_idx], **serialized_updates}
        return updated_goals

    @staticmethod
    def _ensure_heartbeat_in_proof_section(lean_file: LeanFile) -> LeanFile:
        """Ensure the Proof section has an active heartbeat bump."""
        proof = lean_file.get_section("Proof")
        if proof is None:
            return lean_file

        lines = [line.strip() for line in proof.content.splitlines()]
        if any(line.startswith(SET_MAX_HEARTBEATS) for line in lines):
            return lean_file

        lean_file.append_in_section("Proof", SET_MAX_HEARTBEATS, assert_section_present=True)
        return lean_file

    @staticmethod
    def _append_unprocessed_goals_as_sorries(lean_file: LeanFile, goals: list[dict]) -> int:
        """Append all unprocessed goals as sorried theorems to the Proof section."""
        from utils.lean.types import Goal

        sorried_goals: list[str] = []
        for goal_state in goals:
            if goal_state.get("status") != GoalStatus.UNPROCESSED:
                continue
            goal_dict = goal_state["goal"]
            goal_obj = Goal.from_dict(goal_dict) if isinstance(goal_dict, dict) else goal_dict
            sorried_goals.append(goal_obj.as_sorried())

        if sorried_goals:
            lean_file.append_in_section(
                "Proof",
                "\n\n" + "\n\n".join(sorried_goals),
                assert_section_present=True,
            )

        return len(sorried_goals)

    @classmethod
    def _assemble_final_program_content(
        cls,
        current_program: str,
        goals: list[dict],
        grind_gen_param: Optional[int],
        include_unprocessed_sorries: bool = False,
    ) -> tuple[str, int]:
        """Pure final-assembly helper shared by DBOS flow and shutdown hooks."""
        from utils.lean.types import Goal

        lean_file = LeanFile.from_content(current_program)
        injected_sorries = 0
        if include_unprocessed_sorries:
            injected_sorries = cls._append_unprocessed_goals_as_sorries(lean_file, goals)

        method = get_velvet_method(lean_file.get_section('Impl', assert_exists=True).content)
        prove_correct_block = get_prove_correct_block(method)
        final_prove_correct_block = prove_correct_block
        if grind_gen_param is not None:
            final_prove_correct_block = (
                build_custom_loom_solver_prelude(grind_gen_param).strip()
                + "\n\n"
                + final_prove_correct_block
            )

        goal_tactics = []
        for goal_state in goals:
            goal_dict = goal_state["goal"]
            goal_obj = Goal.from_dict(goal_dict) if isinstance(goal_dict, dict) else goal_dict
            goal_tactics.append(indent(exact_goal(goal_obj), 2))

        if goal_tactics:
            tactics_block = "\n" + "\n".join(goal_tactics)
            pattern = re.escape(LOOM_SOLVE_SIMP_ALL)
            replacement = LOOM_SOLVE_SIMP_ALL + tactics_block
            final_prove_correct_block = re.sub(
                pattern,
                replacement,
                final_prove_correct_block,
                count=1,
            )

        lean_file.append_in_section('Proof', final_prove_correct_block, assert_section_present=True)
        return lean_file.reconstruct(), injected_sorries

    def _write_shutdown_assembled_program(
        self,
        file_path: str,
        goals: list[dict],
        grind_gen_param: Optional[int],
    ) -> None:
        """Best-effort shutdown snapshot using the shared final assembler."""
        current_program = Path(file_path).read_text() if Path(file_path).exists() else ""
        final_program, injected_sorries = self._assemble_final_program_content(
            current_program=current_program,
            goals=goals,
            grind_gen_param=grind_gen_param,
            include_unprocessed_sorries=True,
        )
        Path(file_path).write_text(final_program)
        logger.info(
            f"Shutdown snapshot assembled at {file_path} with {injected_sorries} injected sorry goal(s)"
        )

    @shutdown_boundary("before proof orchestrator prepare-goals step")
    @DBOS.step()
    async def _prepare_goals_node(self, state: VelvetAgentState) -> dict:
        """Prepare goals by extracting them after loom_solve.

        1. Add prove_correct with loom_solve temporarily
        2. Query Lean LSP for goals after loom_solve <;> simp_all
        3. Comment out prove_correct and loom_solve
        4. Return parsed goals
        """
        buffer = ProgramBuffer.from_dict(state["program_state"])
        stable_program = buffer.get_stable(assert_exists=True)

        is_valid, error_state = validate_output_file(state)
        if not is_valid:
            return {"goals": []}

        file_path = state.get("output_file", "")
        path = Path(file_path)
        logger.info("=== Preparing Goals ===")

        try:
            extraction_result = await extract_goals_after_loom_solve_with_retry(
                stable_program,
                file_path,
                preprocess=remove_goal_extraction_noise,
                postprocess=self._ensure_heartbeat_in_proof_section,
                section_name="Proof",
                cleanup_mode="clear",  # Keep empty Proof section for downstream prover
                preferred_grind_gen_param=state.get("goal_extraction_grind_gen_param"),
            )
            modified_content = extraction_result.cleaned_content
            goals = extraction_result.goals
            logger.info("TO BE PROVEN")
            for goal in goals:
                logger.info(f"{goal.as_sorried()}")
            logger.info(f"Found {len(goals)} goal(s) after loom_solve <;> simp_all")

            goal_states: list[GoalState] = []
            for goal in goals:
                goal_state: GoalState = {
                    "goal": goal.to_dict(),  # Serialize for DBOS persistence
                    "status": GoalStatus.UNPROCESSED,
                    "description": "",
                    "failures": [],
                    "proof_result": None
                }
                goal_states.append(goal_state)

            logger.info(f"=== Prepared {len(goal_states)} goal(s) for proving ===")

            return {
                "goals": goal_states,
                "goal_extraction_grind_gen_param": extraction_result.grind_gen_param,
                "program_state": self._update_buffer_from_content(
                    buffer,
                    modified_content,
                )
            }

        except Exception as e:
            logger.error(f"Error during goal preparation: {e}")
            path.write_text(stable_program)
            return {
                "goals": [],
                "program_state": self._update_buffer_from_content(
                    buffer,
                    stable_program,
                )
            }

    # NOTE: No @DBOS.step() here - the graph nodes (_prepare_goals_node, _prove_goal_node, etc.)
    # call prove_goal which is a @DBOS.workflow(). DBOS doesn't allow starting a new workflow
    # from within a step that's inside a workflow. The individual nodes that need checkpointing
    # are already decorated with @DBOS.step() (_prepare_goals_node, _assemble_final_node).
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph."""
        return await self.graph.ainvoke(state, {"recursion_limit": 150})

    def build_graph(self) -> StateGraph:
        """Build proof orchestration graph."""
        workflow = StateGraph(VelvetAgentState)

        # Nodes for goal processing
        workflow.add_node("prepare_goals", self._prepare_goals_node)
        workflow.add_node("route_goals", self._route_goals_node)
        workflow.add_node("prove_goal", self._prove_goal_node)
        workflow.add_node("assemble_final", self._assemble_final_node)

        # First prepare goals (uncomment loom_solve, extract goals)
        workflow.add_edge(START, "prepare_goals")
        workflow.add_edge("prepare_goals", "route_goals")

        # Conditional edge: either prove a goal or move to final assembly
        def should_process_goal(state: VelvetAgentState) -> str:
            """Check if there's a goal to process."""
            goals = state.get("goals", [])
            for goal in goals:
                if goal["status"] == GoalStatus.UNPROCESSED:
                    return "prove_goal"
            return "assemble_final"

        workflow.add_conditional_edges("route_goals", should_process_goal)
        workflow.add_edge("prove_goal", "route_goals")
        workflow.add_edge("assemble_final", END)

        return workflow

    async def _route_goals_node(self, state: VelvetAgentState) -> dict:
        """Route to the next unprocessed goal."""
        from utils.shutdown import handle_shutdown_if_requested

        # Check for shutdown before processing next goal
        handle_shutdown_if_requested("between goal processing")

        goals = state.get("goals", [])

        if not goals:
            logger.warning("No goals found in state")
            return {}

        # Count the status
        unprocessed = sum(1 for g in goals if g["status"] == GoalStatus.UNPROCESSED)
        proven = sum(1 for g in goals if g["status"] == GoalStatus.PROVEN)
        failed = sum(1 for g in goals if g["status"] == GoalStatus.FAILED)

        logger.info(f"Goal processing summary: {proven} proven, {failed} failed, {unprocessed} unprocessed out of {len(goals)} total")
        return {}

    # NOTE: No @DBOS.step() — this node calls prove_goal (a child @DBOS.workflow),
    # and DBOS forbids starting a workflow from within a step. The file write at
    # the end (Path.write_text) is necessary because prove_goal's _finalize_result
    # is a @DBOS.step() whose file-write side effect is skipped on replay — the
    # explicit write here ensures the file matches result.content regardless of
    # whether prove_goal ran fresh or replayed cached steps.
    async def _prove_goal_node(self, state: VelvetAgentState) -> dict:
        """Prove a goal using recursive decomposition prover."""
        file_path = state.get("output_file", "")
        goals = state.get("goals", [])
        buffer = ProgramBuffer.from_dict(state["program_state"])
        stable_program = buffer.get_stable(assert_exists=True)

        # Find the first unprocessed goal
        goal_idx = -1
        current_goal = None
        for i, goal in enumerate(goals):
            if goal["status"] == GoalStatus.UNPROCESSED:
                goal_idx = i
                current_goal = goal
                break

        if current_goal is None:
            logger.warning("No unprocessed goal found")
            return {}

        # Deserialize Goal from dict (DBOS persistence)
        from utils.lean.types import Goal
        goal_dict = current_goal["goal"]
        goal_obj = Goal.from_dict(goal_dict) if isinstance(goal_dict, dict) else goal_dict
        logger.info(f"{'='*80}")
        logger.info(f"Proving goal {goal_idx}: {goal_obj.name}")
        logger.info(f"{'='*80}")

        logger.info(f"GOAL THEOREM TO PROVE:\n{goal_obj.as_sorried()}")

        # Invoke the configured prover with recursive decomposition
        from config.limits import Limits

        from utils.proof_types import (
            PantographParams,
            AttemptBudgetConfigBundle,
            AttemptBudgetConfig,
            AttemptBudgetMode,
        )
        project_path = find_project_root(file_path)
        from utils.lean.constants import VELVET_AUTOMATION
        from utils.context_utils import SpecsImplProofSignaturesExtractor
        attempt_budgets = AttemptBudgetConfigBundle(
            shallow=AttemptBudgetConfig(
                mode=AttemptBudgetMode.UP,
                base=5,
                slope=2,
                min_attempts=5,
                max_attempts=15,
            ),
            decomposition=AttemptBudgetConfig(
                mode=AttemptBudgetMode.DOWN,
                base=10,
                slope=2,
                min_attempts=5,
                max_attempts=10,
            ),
        )

        ctx = ProvingContext(
            file_path=file_path,
            goal=goal_obj,
            sections=["Specs", "Proof"],
            pantograph=PantographParams(
                key=goal_obj.name,
                project_path=project_path,
                imports=VELVET_IMPORTS,
                options=PANTOGRAPH_OPTIONS,
                core_options=PANTOGRAPH_CORE_OPTIONS,
            ),
            automation_tactics=VELVET_AUTOMATION,
            informal_reasoning="",
            context_extractor=SpecsImplProofSignaturesExtractor(),
            attempt_budgets=attempt_budgets,
            hint_sections=["Specs"],
        )

        try:
            with shutdown_hook(
                ShutdownHookMode.CLEAR_AND_PUSH,
                lambda: self._write_shutdown_assembled_program(
                    file_path=file_path,
                    goals=goals,
                    grind_gen_param=state.get("goal_extraction_grind_gen_param"),
                ),
            ):
                result = await self.prover.prove(
                    ctx=ctx,
                    max_depth=Limits.PROOF_GUIDE_MAX_DEPTH,
                )
        finally:
            PantographFactory.cleanup(ctx.pantograph.key)

        # Use filtered_goal from result if available (unused params removed)
        final_goal = result.filtered_goal if result.filtered_goal else goal_obj

        Path(file_path).write_text(result.content)

        # Update goal status based on result
        if result.success:
            if result.has_sorry:
                logger.info(f"⚠ Goal {goal_obj.name} PROVEN with sorry placeholders (partial success)")
                logger.info(f"Failure summary:\n{result.get_failure_summary()}")

                # Mark as PARTIAL - proof exists in file but contains sorries
                updated_goals = self._update_goal(
                    goals, goal_idx,
                    status=GoalStatus.PARTIAL,
                    description=f"Partial proof with {len(result.failures)} sorry placeholders",
                    failures=result.failures,
                    proof_result=result,
                    goal=final_goal,  # Update with filtered goal (unused params removed)
                )

                return {
                    "goals": updated_goals,
                    "program_state": self._update_buffer_from_content(
                        buffer,
                        result.content,
                    )
                }
            else:
                logger.info(f"✓ Goal {goal_obj.name} PROVEN successfully!")

                updated_goals = self._update_goal(
                    goals, goal_idx,
                    status=GoalStatus.PROVEN,
                    description="Proved with recursive decomposition",
                    failures=[],
                    goal=final_goal,  # Update with filtered goal (unused params removed)
                )

                # Save to phase_results
                phase_results = state.get("phase_results", {}).copy()
                phase_results[self.name] = {
                    "stable_content": result.content,
                }

                return {
                    "goals": updated_goals,
                    "program_state": self._update_buffer_from_content(
                        buffer,
                        result.content,
                    ),
                    "phase_results": phase_results
                }
        else:
            logger.error(f"✗ Goal {goal_obj.name} FAILED: {result.error}")
            logger.error(f"Failure summary:\n{result.get_failure_summary()}")

            # Mark as failed (keep original goal, no filtering for failures)
            updated_goals = self._update_goal(
                goals, goal_idx,
                status=GoalStatus.FAILED,
                description=f"Proof failed: {result.error[:200]}",
                failures=result.failures,
                proof_result=result
            )

            # Use result.content which contains the sorried theorem written by prover_agent
            return {
                "goals": updated_goals,
                "program_state": self._update_buffer_from_content(
                    buffer,
                    result.content,
                )
            }

    @shutdown_boundary("before proof orchestrator assemble-final step")
    @DBOS.step()
    async def _assemble_final_node(self, state: VelvetAgentState) -> dict:
        """Deterministically assemble the final proof.

        This:
        1. Moves prove_correct and loom_solve blocks to end of file
        2. Uncomments them
        3. Adds goal applications after loom_solve cleanup/expose_names
        4. Typechecks and counts sorries
        """

        from utils.lean.parser import _remove_comments

        goals = state.get("goals", [])
        buffer = ProgramBuffer.from_dict(state["program_state"])
        stable_program = buffer.get_stable(assert_exists=True)
        file_path = state.get("output_file", "")

        logger.info("=== Final Deterministic Assembly ===")

        current_program = stable_program

        # Steps 1-3: Shared deterministic assembly logic
        logger.info("Assembling final proof program")
        final_program, _ = self._assemble_final_program_content(
            current_program=current_program,
            goals=goals,
            grind_gen_param=state.get("goal_extraction_grind_gen_param"),
        )
        Path(file_path).write_text(final_program)

        # Step 4: Typecheck and count sorries
        logger.info("Step 4: Typechecking final assembled proof")
        sorry_count = _remove_comments(final_program).count("sorry")
        logger.info(f"Final proof contains {sorry_count} sorry/sorries")

        # Run typecheck
        typecheck_result = lean_build_file_helper(file_path)

        if typecheck_result.typechecks:
            logger.info(f"✓ Final assembled proof typechecks successfully! ({sorry_count} sorries)")
        else:
            logger.error("✗ Final assembled proof failed to typecheck")

        # Save phase results
        phase_results = state.get("phase_results", {}).copy()
        phase_results[self.name] = {
            "stable_content": final_program,
            "build_log": typecheck_result.build_log,
            "typechecks": typecheck_result.typechecks
        }

        return {
            "program_state": buffer.update_current(
                final_program,
                promote_to_stable=True,
            ),
            "build_log": typecheck_result.build_log,
            "typechecks": typecheck_result.typechecks,
            "phase_results": phase_results,
        }

    @staticmethod
    def _update_buffer_from_content(
        buffer: ProgramBuffer,
        content: str,
    ) -> dict:
        """Set buffer content as current+stable and return serialized state.

        Note: this mutates the passed buffer (and the underlying state dict).
        """
        return buffer.update_current(content, promote_to_stable=True)


def main():
    """Entry point for lloom-agent-proof-orchestrator CLI command."""
    VelvetProofOrchestratorAgent.main()


if __name__ == "__main__":
    main()
