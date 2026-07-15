import asyncio
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional, TYPE_CHECKING

from dbos import DBOS
from utils.lean.parser import LeanFile
from utils.validation_result import ValidationResult
from utils.differ import Differ
from langchain_core.messages import HumanMessage
from langgraph.graph import StateGraph, START, END

from agents.agent_state import JudgeVerdict, VelvetAgentState, RetryLimitExceeded
from agents.base import BaseAgent
from agents.proof_reasoning_agent import ProofReasoningAgent
from agents.velvet_judge import VelvetJudgeAgent
from tools.common import (
    lean_build_file_helper,
    write_method,
    check_velvet_method,
)
from utils.validation import validate_output_file
from utils.shutdown import shutdown_boundary
from logging_config import get_logger
from utils.message_helpers import create_prompt, code_block, dynamic, lean_block, section, stable
from utils.velvet_helpers import (
    GoalExtractionError,
    get_velvet_method,
    normalize_body_with_while_tags,
    extract_goals_after_loom_solve_with_retry,
    remove_goal_extraction_noise,
    identity,
    get_pbt_counterexamples,
    format_pbt_feedback,
)
from utils.velvet_helpers import (
    partition_invariant_goals,
    format_correctness_feedback,
    format_invariant_strength_feedback,
)
from utils.analytics.velvet_invariant_inferrer import (
    AttemptMeta,
    AttemptOutcome,
    CorrectnessGoalKind,
    CorrectnessSummary as InferrerCorrectnessAnalytics,
    CorrectnessVerdict,
    LLMGoalResult as InferrerLLMGoalAnalytics,
    TypecheckSummary as InferrerTypecheckAnalytics,
    write_attempt_meta,
    write_correctness_summary,
    write_typecheck_summary,
)
from config.limits import Limits
from tools.pantograph_client import PantographClient, PantographFactory
from tools.automation import DischargeResult, discharge_goals, try_plausible
from agents.retriever_agent import (
    RetrieverAgent,
    DiscoveryConfig,
)
from tools.proof_search import (
    LemmaDiscoveryConfig,
    WeightedTactic,
    build_tactic_pool,
)
from utils.lean.constants import (
    PANTOGRAPH_CORE_OPTIONS,
    PANTOGRAPH_OPTIONS,
    VELVET_AUTOMATION,
    VELVET_IMPORTS,
)
from utils.lean.build import find_project_root
from utils.program_state import ProgramBuffer
from utils.proof_types import NewPantographClient, PantographParams

if TYPE_CHECKING:
    from agents.velvet_judge import VelvetJudgeAgent
    from utils.proof_types import ProofHints
    from providers import LLMConfig, ReasoningLevel
from providers import ReasoningLevel
from utils.escalation import AttemptContext

logger = get_logger(__name__)

# Prompt constants
LEAN_BUILD_TOOL = """**Fast Velvet Check Tool Available:**
- `check_velvet_method`: Check a Velvet method snippet in the current problem context.
  Assumes the relevant Specs are already available for this problem."""

WRITE_METHOD_RULES = """- Use the `write_method` tool to write ONLY the method with invariants
- The tool will automatically place it in the Impl section (other sections are preserved)
- Output ONLY the method (with invariants), NOT imports or other sections
- Do NOT call write_method multiple times
- After writing, immediately respond with ONLY the text 'Done' and make NO MORE TOOL CALLS"""

RETRY_STRATEGY_BATCH_SIZE = 5
PRE_INVARIANT_INFERRER_PHASE_KEY = "pre_invariant_inferrer"


@dataclass(frozen=True)
class ExtractedInvariantGoals:
    invariant_goals: list
    non_invariant_goals: list
    grind_gen_param: int | None


@DBOS.dbos_class()
class VelvetInvariantInferrerAgent(BaseAgent):
    """Agent that discovers loop invariants for Velvet programs."""

    name = "velvet_invariant_inferrer"
    description = "Discovers loop invariants for a velvet program. Tries to add better invariants so that it's easier for the automation to discharge the proof."

    system_prompt: str = ""
    max_attempts: int = Limits.VELVET_INVARIANT_MAX_ATTEMPTS
    max_judge_rejections: int = Limits.MAX_JUDGE_REJECTIONS_PER_AGENT

    # Additional context files to inject into system prompt
    additional_context_files = ["prompts/velvet_documentation.md"]

    def __init__(
        self,
        config: "LLMConfig",
        *,
        judge: "VelvetJudgeAgent",
        reasoning: "ProofReasoningAgent",
        retriever: "RetrieverAgent",
        max_attempts: int = Limits.VELVET_INVARIANT_MAX_ATTEMPTS,
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self.max_attempts = max_attempts
        self.judge = judge
        self.reasoning_agent = reasoning
        self.retriever = retriever
        self._inferrer_tactic_pool: Optional[list[WeightedTactic]] = None
        self._proof_hints: Optional["ProofHints"] = None

        from utils.prompt_helpers import load_system_prompt
        self.system_prompt = load_system_prompt(
            "velvet_invariant_inferrer.md",
            "You are a Velvet programming expert. Generate correct Lean/Velvet code from specifications.",
        )
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    async def get_tools(self) -> list:
        return [write_method, check_velvet_method]

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state, {"recursion_limit": 100})

    def build_graph(self) -> StateGraph:
        """Build the generate -> typecheck -> judge loop graph."""
        logger.info("Building VelvetInvariantInferrerAgent graph")

        builder = StateGraph(VelvetAgentState)

        # Add nodes
        builder.add_node("loop_analysis", self._analyze_loops)
        builder.add_node("snapshot_pre_inferrer", self._snapshot_pre_inferrer_node)
        builder.add_node("generate", self._infer_node)
        builder.add_node("typecheck", self._typecheck_node)
        builder.add_node("judge", self._judge_node)
        builder.add_node("setup_retry_after_judge", self._setup_retry_after_judge_node)

        # Flow: START -> loop_analysis
        builder.add_edge(START, "loop_analysis")
        builder.add_conditional_edges(
            "loop_analysis",
            lambda st: "CONTAINS_LOOPS" if st.get("has_loops") else "NO_LOOPS",
            {"CONTAINS_LOOPS": "snapshot_pre_inferrer", "NO_LOOPS": END},
        )
        builder.add_edge("snapshot_pre_inferrer", "generate")

        # Flow: generate -> typecheck
        builder.add_edge("generate", "typecheck")

        # After typecheck: if pass -> judge, if fail -> retry
        builder.add_conditional_edges(
            "typecheck",
            self._should_continue_after_typecheck,
            {"retry": "generate", "judge": "judge"},
        )

        # After judge: if pass -> done, if fail -> retry
        builder.add_conditional_edges(
            "judge",
            self._should_continue_after_judge,
            {"retry": "setup_retry_after_judge", "done": END},
        )
        builder.add_edge("setup_retry_after_judge", "generate")

        logger.info("Graph built: START -> loop_analysis -> generate -> typecheck -> judge -> (retry|done)")
        return builder

    @shutdown_boundary("before inferrer loop-analysis step")
    @DBOS.step()
    def _analyze_loops(self, state: VelvetAgentState) -> dict:
        """Check if the Velvet method has while loops.

        Sets 'has_loops' in state for routing decision.
        """
        buffer = ProgramBuffer.from_dict(state["program_state"])
        stable_program = buffer.get_stable(assert_exists=True)
        method = get_velvet_method(
            LeanFile.from_content(stable_program)
            .get_section("Impl", assert_exists=True)
            .content
        )
        has_loops = method.has_while_loop()
        logger.info(f"Method '{method.name}' has_while_loop: {has_loops}")

        if not has_loops:
            logger.info(
                "No while loops found - skipping invariant generation and also marking judge verdict as not required"
            )
            return {"has_loops": False, "judge_verdict": JudgeVerdict.NOT_REQUIRED}

        return {"has_loops": True}

    @shutdown_boundary("before inferrer snapshot step")
    @DBOS.step()
    def _snapshot_pre_inferrer_node(self, state: VelvetAgentState) -> dict:
        """Persist the first pre-inferrer program snapshot for validation."""
        phase_results = dict(state.get("phase_results", {}))
        if PRE_INVARIANT_INFERRER_PHASE_KEY in phase_results:
            return {}

        buffer = ProgramBuffer.from_dict(state["program_state"])
        baseline_program = buffer.get_current()
        lean_file = LeanFile.from_content(baseline_program)
        lean_file.get_section("Specs", assert_exists=True)
        lean_file.get_section("Impl", assert_exists=True)
        phase_results[PRE_INVARIANT_INFERRER_PHASE_KEY] = {"content": baseline_program}
        logger.info("Captured pre-inferrer baseline snapshot")
        return {"phase_results": phase_results}

    def _get_section(self, program: str, section: str) -> str:
        """Extract a section from a program."""
        lean_file = LeanFile.from_content(program)
        return lean_file.get_section(section, assert_exists=True).content

    def _get_baseline_content(
        self,
        state: VelvetAgentState,
    ) -> str:
        """Get the inferrer's immutable pre-inferrer baseline program content."""
        phase_results = state.get("phase_results", {})
        baseline_entry = phase_results.get(PRE_INVARIANT_INFERRER_PHASE_KEY, {})
        baseline_content = baseline_entry.get("content") if isinstance(baseline_entry, dict) else None
        if baseline_content:
            return baseline_content

        raise ValueError(
            f"Missing required phase_results['{PRE_INVARIANT_INFERRER_PHASE_KEY}'] baseline snapshot"
        )

    @staticmethod
    def _should_reset_retry_strategy(attempt_index: int) -> bool:
        """Restart the invariant-design strategy every few failed attempts."""
        return attempt_index > 0 and attempt_index % RETRY_STRATEGY_BATCH_SIZE == 0

    async def _ensure_pantograph_default_context(
        self, state: VelvetAgentState
    ) -> PantographClient:
        """Ensure a default Pantograph client exists with the current Specs loaded."""
        output_file = state["output_file"]
        key = f"inferrer_{output_file}"

        project_path = find_project_root(output_file)
        client = PantographFactory.resolve_client(
            source=PantographParams(
                key=key,
                project_path=project_path,
                imports=VELVET_IMPORTS,
                options=PANTOGRAPH_OPTIONS,
                core_options=PANTOGRAPH_CORE_OPTIONS,
            ),
            make_default=True,
        )

        specs_load_key = f"{key}:Specs"
        if not any(load_key == specs_load_key for load_key, _ in client.get_load_log()):
            buffer = ProgramBuffer.from_dict(state["program_state"])
            program = buffer.get_current()
            specs = (
                LeanFile.from_content(program)
                .get_section("Specs", assert_exists=True)
                .full_text()
            )
            await client.load_definitions(specs_load_key, specs)

        return client

    @shutdown_boundary("before inferrer generate step")
    @DBOS.step()
    async def _infer_node(self, state: VelvetAgentState) -> dict:
        """Generate or refine the Velvet program using LLM with tools."""

        attempt = state["attempt"] + 1
        logger.info(f"Generation attempt {attempt}/{self.max_attempts}")

        try:
            await self._ensure_pantograph_default_context(state)
        except Exception as e:
            logger.warning(f"Failed to prepare Pantograph method-check context: {e}")

        # Ensure output file exists (should be from programmer stage)
        output_path = Path(state["output_file"])
        if not output_path.exists():
            raise RuntimeError(
                f"Output file does not exist: {output_path}. Inferrer requires file from programmer stage."
            )

        # Build fresh messages for this invocation
        messages = []
        self.ensure_system_messages(messages)

        # Extract Specs and current Impl
        buffer = ProgramBuffer.from_dict(state["program_state"])
        current_content = buffer.get_current()
        specs = self._get_section(current_content, "Specs")
        current_impl = self._get_section(current_content, "Impl")

        stable_context_sections = {
            "Specification": lean_block(specs),
        }
        if state.get("continuation_ctx"):
            stable_context_sections = {
                **stable_context_sections,
                **state.get("continuation_ctx")
            }

        if state["attempt"] == 0:
            # First attempt
            logger.info("Mode: Initial attempt")

            prompt = create_prompt(
                task=stable("Please help improve the loop invariants (if any) in our given Velvet/Lean program."),
                sections=tuple(
                    list(section(k, stable(v)) for k, v in stable_context_sections.items())
                    + [section("Current Implementation", stable(lean_block(current_impl)))]
                ),
                instructions=stable(f"""{LEAN_BUILD_TOOL}

The output file should be written to: {state["output_file"]}

**CRITICAL INSTRUCTION:**
{WRITE_METHOD_RULES}"""),
                closing=stable("Focus on correctness and type safety. The code must typecheck."),
            )
        else:
            # Retry: Build a self-sufficient message with all necessary context
            logger.info("Mode: Refinement based on type errors and judge feedback")

            baseline_content = self._get_baseline_content(state)
            stable_impl = self._get_section(baseline_content, "Impl")
            reset_retry_strategy = self._should_reset_retry_strategy(state["attempt"])
            dynamic_context_sections = {
                "Current Implementation": lean_block(current_impl),
            }
            if state.get("judge_reasoning"):
                dynamic_context_sections["Judge Feedback from Previous Attempt"] = (
                    state["judge_reasoning"]
                    + "\n\nThe judge evaluated your previous attempt and found issues. Please address the feedback above."
                )
            if reset_retry_strategy:
                logger.info(
                    "Retry batch boundary reached at attempt %s - restarting invariant strategy",
                    state["attempt"],
                )
                dynamic_context_sections["Previous Attempt That Failed"] = lean_block(current_impl)
            else:
                pass
            dynamic_context_sections["Baseline Implementation to Preserve"] = lean_block(stable_impl)
            dynamic_context_sections["Build Errors"] = state["build_log"]

            strategy_reset_guidance = ""
            if reset_retry_strategy:
                strategy_reset_guidance = (
                    f"\n\nThis is a strategy reset after {RETRY_STRATEGY_BATCH_SIZE} failed attempts. "
                    "Do not make another small local edit to the previous invariants. Treat the previous "
                    "invariant set as a failed direction. Take a step back, think about the problem from "
                    "scratch, and synthesize a fresh set of invariants from the specification, method body, "
                    "and feedback."
                )

            prompt_sections = tuple(
                section(k, stable(v)) for k, v in stable_context_sections.items()
            ) + tuple(
                section(k, dynamic(v)) for k, v in dynamic_context_sections.items()
            ) + (
                section(
                    "Issues To Address",
                    dynamic("The previous program had issues. Please fix them."),
                ),
                section(
                    "Retry Instructions",
                    dynamic(
                        'The "Baseline Implementation to Preserve" section is the last accepted implementation text that you should preserve outside the allowed annotation edits.\n\n'
                        "If the previous invariants are misguided, brittle, or conflict with the feedback, you should rethink them and replace them substantially rather than making only small local edits. "
                        "You do not need to stay on the same path just because it was tried before. If your previous strategy seems fundamentally off, change direction and use a different invariant design. "
                        "When feedback shows that an invariant is false, first consider weakening or removing that invariant instead of introducing disjunctions, implications, or verifier-state encodings unless they are clearly necessary. "
                        "You may deviate from the previous invariant design as long as you preserve every non-annotation line exactly."
                        f"{strategy_reset_guidance}"
                    ),
                ),
            )
            prompt = create_prompt(
                task=stable("Please help improve the loop invariants (if any) in our given Velvet/Lean program."),
                sections=prompt_sections,
                instructions=stable(f"""{LEAN_BUILD_TOOL}

The output file should be written to: {state["output_file"]}

**CRITICAL INSTRUCTION:**
{WRITE_METHOD_RULES}"""),
                closing=stable("Focus on correctness and type safety. The code must typecheck."),
            )

        self.append_prompt(messages, prompt)

        response = await self.invoke_with_tools(
            messages,
            max_iterations=Limits.VELVET_INVARIANT_MAX_ITERATIONS,
            reasoning_level=self._select_reasoning_level(
                AttemptContext(
                    attempt_index=state["attempt"],
                    max_attempts=self.max_attempts,
                )
            ),
        )

        # Read the file that was written to get the program
        if state["output_file"] and Path(state["output_file"]).exists():
            program = Path(state["output_file"]).read_text()
            logger.info(f"Generated program written to {state['output_file']}")
        else:
            # Fallback: use response content if file wasn't written
            program = response.content
            logger.warning("Output file not found, using LLM response content directly")

        return {
            "program_state": buffer.update_current(program),
            "attempt": state["attempt"] + 1,
            "previous_attempt_impl": current_impl,
        }

    @staticmethod
    def _select_reasoning_level(attempt_ctx: AttemptContext) -> ReasoningLevel | None:
        """Select inferrer reasoning level by repeating retry pattern.

        The reasoning schedule repeats per attempt as:

        LOW | LOW | LOW | MEDIUM | MEDIUM | ...
        """
        attempt_in_cycle = attempt_ctx.attempt_index % RETRY_STRATEGY_BATCH_SIZE
        if attempt_in_cycle >= RETRY_STRATEGY_BATCH_SIZE - 2:
            return ReasoningLevel.MEDIUM
        return ReasoningLevel.LOW

    def _current_attempt_reasoning_level(self, state: VelvetAgentState) -> ReasoningLevel:
        """Return the effective reasoning level used for the current attempt."""
        selected = self._select_reasoning_level(
            AttemptContext(
                attempt_index=max(0, state["attempt"] - 1),
                max_attempts=self.max_attempts,
            )
        )
        return selected if selected is not None else self._reasoning_level

    def _record_typecheck_analytics(
        self,
        state: VelvetAgentState,
        *,
        validation_passed: bool,
        typecheck_result: dict[str, Any],
    ) -> None:
        """Store the inferrer typecheck summary for one attempt."""
        diagnostics = typecheck_result.get("diagnostics", [])
        pbt_counterexamples = get_pbt_counterexamples(diagnostics)
        program_text = ProgramBuffer.from_dict(state["program_state"]).get_current()
        impl_text = LeanFile.from_content(program_text).get_section(
            "Impl", assert_exists=True
        ).full_text()

        payload = InferrerTypecheckAnalytics(
            validation_passed=validation_passed,
            build_passed=bool(typecheck_result.get("typechecks", False)),
            pbt_failure=bool(pbt_counterexamples),
            program=program_text,
            impl_section=impl_text,
            pbt_failure_message=(
                "\n".join(diagnostic.message for diagnostic in pbt_counterexamples)
                if pbt_counterexamples
                else None
            ),
        )

        attempt_log = self._analytics_attempt(state)
        write_typecheck_summary(
            attempt_log,
            payload,
            text=str(typecheck_result.get("build_log", "")),
        )

    def _record_correctness_analytics(
        self,
        state: VelvetAgentState,
        payload: InferrerCorrectnessAnalytics,
        *,
        text: str | None = None,
    ) -> None:
        """Store the inferrer correctness-check summary for one attempt."""
        write_correctness_summary(self._analytics_attempt(state), payload, text=text)

    @staticmethod
    def _typecheck_failure_outcome(typecheck_result: dict[str, Any]) -> AttemptOutcome:
        """Classify inferrer typecheck failure from diagnostics/logs."""
        diagnostics = typecheck_result.get("diagnostics", [])
        if get_pbt_counterexamples(diagnostics):
            return AttemptOutcome.PBT_FAILURE
        return AttemptOutcome.BUILD_FAILURE

    def _finish_attempt(
        self,
        state: VelvetAgentState,
        *,
        final_outcome: AttemptOutcome,
        error_message: str | None = None,
    ) -> None:
        """Write attempt-level completion metadata."""
        reasoning_level = self._current_attempt_reasoning_level(state)
        write_attempt_meta(
            self._analytics_attempt(state),
            AttemptMeta(
                final_outcome=final_outcome,
                reasoning_level=reasoning_level.value,
                error_message=error_message,
                file_path=state["output_file"]
            ),
        )

    @staticmethod
    def _serialize_correctness_result(
        *,
        kind: CorrectnessGoalKind,
        goal_id: str,
        label: str,
        goal_statement: str,
        result: Any,
    ) -> InferrerLLMGoalAnalytics:
        """Normalize one LLM correctness result for analytics storage."""
        return InferrerLLMGoalAnalytics(
            kind=kind,
            goal_id=goal_id,
            label=label,
            goal_statement=goal_statement,
            is_provable=result.is_provable,
            justification=result.justification,
            correction_hint=result.correction_hint,
            success=result.success,
            error=result.error,
        )

    async def _ensure_pantograph_setup(
        self, state: VelvetAgentState
    ) -> tuple[PantographClient, list[WeightedTactic]]:
        """Get or create a PantographClient with Specs loaded and tactic pool built.

        Uses RetrieverAgent.discover_proof_hints() on a fresh Pantograph client for
        symbol discovery, while keeping the factory-keyed client available for fast
        method checks with Specs already loaded.

        Returns (client, tactic_pool).
        """
        output_file = state["output_file"]
        client = await self._ensure_pantograph_default_context(state)

        if not self._inferrer_tactic_pool:
            buffer = ProgramBuffer.from_dict(state["program_state"])
            program = buffer.get_current()
            lean_file = LeanFile.from_content(program)
            specs = lean_file.get_section("Specs", assert_exists=True).full_text()
            project_path = find_project_root(output_file)

            result = await self.retriever.discover_proof_hints(
                source=NewPantographClient(
                    project_path=project_path,
                    imports=VELVET_IMPORTS,
                    options=PANTOGRAPH_OPTIONS,
                    core_options=PANTOGRAPH_CORE_OPTIONS,
                ),
                code=specs,
                config=DiscoveryConfig(
                    dep_graph_depth=1,
                    lemma_discovery=LemmaDiscoveryConfig(),
                ),
            )

            self._proof_hints = result
            self._inferrer_tactic_pool = build_tactic_pool(
                [l.name for l in result.discovered_lemmas],
                result.user_constants,
                result.user_constructors,
            )
            logger.info(f"Tactic pool ready: {len(self._inferrer_tactic_pool)} tactics")

        return client, self._inferrer_tactic_pool

    async def _discharge_goals_mechanically(self, state, all_goals) -> DischargeResult:
        """Try to discharge goals via automation + MCTS."""
        try:
            client, tactic_pool = await self._ensure_pantograph_setup(state)
        except Exception as e:
            raise RuntimeError(f"Pantograph setup failed during mechanical discharge: {e}") from e

        return await discharge_goals(client, tactic_pool, all_goals, VELVET_AUTOMATION)

    async def _extract_goals(
        self, state: VelvetAgentState
    ) -> ExtractedInvariantGoals | None:
        """Extract invariant and non-invariant goals from the current program.

        Returns extracted invariant/non-invariant goals and extraction metadata,
        or None if nothing can be checked.
        """
        buffer = ProgramBuffer.from_dict(state["program_state"])
        program = buffer.get_current()
        output_file = state.get("output_file", "")

        if not output_file or not program:
            logger.info("Skipping check: missing output_file or program")
            return None

        logger.info("Extracting goals after loom_solve")
        grindable_lemmas = self._proof_hints.grindable_lemmas if self._proof_hints else []
        extraction_result = await extract_goals_after_loom_solve_with_retry(
            program,
            output_file,
            preprocess=remove_goal_extraction_noise,
            postprocess=identity,
            hints_lemmas=grindable_lemmas,
            preferred_grind_gen_param=state.get("goal_extraction_grind_gen_param"),
        )
        goals = extraction_result.goals

        invariant_goals, non_invariant_goals = partition_invariant_goals(goals)
        logger.info(
            f"Found {len(invariant_goals)} invariant goals and "
            f"{len(non_invariant_goals)} non-invariant goals to check"
        )

        return ExtractedInvariantGoals(
            invariant_goals=invariant_goals,
            non_invariant_goals=non_invariant_goals,
            grind_gen_param=extraction_result.grind_gen_param,
        )

    async def _discharge_goals(
        self, state: VelvetAgentState, invariant_goals: list, non_invariant_goals: list
    ) -> tuple[list, list]:
        """Discharge goals mechanically via automation tactics + MCTS.

        Returns (undischarged_inv, undischarged_non).
        """
        inv_result = await self._discharge_goals_mechanically(state, invariant_goals) if invariant_goals else DischargeResult()
        non_result = await self._discharge_goals_mechanically(state, non_invariant_goals) if non_invariant_goals else DischargeResult()

        return inv_result.undischarged, non_result.undischarged

    async def _check_plausible(
        self, state: VelvetAgentState, undischarged_inv: list, undischarged_non: list
    ) -> Optional[str]:
        """Phase 4: Try to disprove goals via counter-example search.

        Returns feedback string if a counter-example is found, None otherwise.
        """
        client, _ = await self._ensure_pantograph_setup(state)
        for goal_wrapper, kind in [(g, "invariant") for g in undischarged_inv] + \
                                   [(g, "non_invariant") for g in undischarged_non]:
            try:
                has_counter, build_result = await try_plausible(client, goal_wrapper.goal)
            except Exception as e:
                logger.warning(f"Plausible check failed for {goal_wrapper.goal.name}: {e}")
                continue
            if has_counter:
                label = f"invariant `{goal_wrapper.invariant_name}`" if kind == "invariant" \
                    else f"{goal_wrapper.goal_type} goal"
                return (
                    f"## Disproved Goal\n\n"
                    f"Counter-example found for {label}.\n\n"
                    f"{code_block(build_result.as_string())}"
                )
        return None

    @DBOS.step()
    async def _check_goals_via_llm(
        self, state: VelvetAgentState, undischarged_inv: list, undischarged_non: list
    ) -> tuple[Optional[str], list[InferrerLLMGoalAnalytics]]:
        """Phase 5: LLM correctness/strength check on remaining goals.

        Returns (feedback string if unprovable goals are found, serialized LLM results).
        """
        from agents.proof_reasoning_agent import GoalCheckInput

        buffer = ProgramBuffer.from_dict(state["program_state"])
        program = buffer.get_current()
        lean_file = LeanFile.from_content(program)
        spec = lean_file.get_section("Specs", assert_exists=True).content
        impl = lean_file.get_section("Impl", assert_exists=True).content

        shared_context = {
            "Specification": lean_block(spec),
            "Implementation": lean_block(impl),
        }
        if self._proof_hints:
            lemma_hints = self._proof_hints.format_lemmas()
            if lemma_hints:
                shared_context["Available Lemmas and Hints"] = lemma_hints

        feedbacks = []
        llm_results: list[InferrerLLMGoalAnalytics] = []

        inv_goal_inputs = [
            GoalCheckInput(
                goal_id=f"inv_{i}",
                goal_statement=inv_goal.goal.as_theorem(),
                context=f"Invariant `{inv_goal.invariant_name}`: {inv_goal.invariant_statement}",
            )
            for i, inv_goal in enumerate(undischarged_inv, 1)
        ]
        non_goal_inputs = [
            GoalCheckInput(
                goal_id=f"strength_{i}",
                goal_statement=goal.goal.as_theorem(),
                context=(
                    f"This is a {goal.goal_type} goal. "
                    "Evaluate if invariants in premises are SUFFICIENT to prove it. "
                    "If not, suggest what additional properties are needed."
                ),
            )
            for i, goal in enumerate(undischarged_non, 1)
        ]

        inv_results: list = []
        non_results: list = []

        tasks = []
        if inv_goal_inputs:
            logger.info(f"Checking {len(inv_goal_inputs)} undischarged invariant goals via LLM")
            tasks.append(
                self.reasoning_agent.check_goals_correctness_batch(
                    goals=inv_goal_inputs,
                    shared_context=shared_context,
                )
            )
        if non_goal_inputs:
            logger.info(f"Checking {len(non_goal_inputs)} undischarged strength goals via LLM")
            tasks.append(
                self.reasoning_agent.check_goals_correctness_batch(
                    goals=non_goal_inputs,
                    shared_context=shared_context,
                )
            )

        gathered_results = await asyncio.gather(*tasks) if tasks else []
        next_result_idx = 0
        if inv_goal_inputs:
            inv_results = gathered_results[next_result_idx]
            next_result_idx += 1
        if non_goal_inputs:
            non_results = gathered_results[next_result_idx]

        if undischarged_inv:
            for inv_goal, result in zip(undischarged_inv, inv_results):
                llm_results.append(
                    self._serialize_correctness_result(
                        kind=CorrectnessGoalKind.INVARIANT,
                        goal_id=inv_goal.goal.name,
                        label=inv_goal.invariant_name,
                        goal_statement=inv_goal.goal.as_theorem(),
                        result=result,
                    )
                )
                if result.is_provable:
                    continue
                logger.warning(f"Goal '{inv_goal.invariant_name}' NOT provable: {result.justification}")
                feedbacks.append(format_correctness_feedback(
                    inv_goal, result.is_provable, result.justification, result.correction_hint,
                ))

        if feedbacks:
            logger.info("Correctness check failed - skipping invariant strength check")
            return "## Unprovable Invariant Goals\n\n" + "\n".join(feedbacks), llm_results

        if undischarged_non:
            for goal, result in zip(undischarged_non, non_results):
                llm_results.append(
                    self._serialize_correctness_result(
                        kind=CorrectnessGoalKind.NON_INVARIANT,
                        goal_id=goal.goal.name,
                        label=goal.goal_type,
                        goal_statement=goal.goal.as_theorem(),
                        result=result,
                    )
                )
                if result.is_provable:
                    continue
                logger.warning(f"Goal '{goal.goal_type}' NOT provable: {result.justification}")
                feedbacks.append(format_invariant_strength_feedback(
                    goal, result.is_provable, result.justification, result.correction_hint,
                ))

        if feedbacks:
            header = (
                "## Non-Invariant Goals (Invariant Strength Check)\n\n"
                "These goals use invariants in their premises. The invariants may need strengthening.\n\n"
            )
            logger.info("Generated feedback for unprovable goals")
            return header + "\n".join(feedbacks), llm_results

        return None, llm_results

    # NOTE: No @DBOS.step() - this orchestrates the individual steps
    async def _typecheck_node(self, state: VelvetAgentState) -> dict:
        """Orchestrate typecheck and invariant checking steps."""
        logger.info("Running typecheck orchestration")

        validation_passed = False
        typecheck_analytics_result: dict[str, Any]
        correctness_payload: InferrerCorrectnessAnalytics | None = None
        correctness_text: str | None = None
        finish_outcome: AttemptOutcome | None = None
        finish_error_message: str | None = None

        is_valid, error_state = validate_output_file(state)
        if not is_valid:
            final_result = error_state
            typecheck_analytics_result = {
                "typechecks": False,
                "diagnostics": [],
                "build_log": str(error_state.get("build_log", "Output file validation failed")),
            }
            finish_outcome = AttemptOutcome.INVALID_OUTPUT_FILE
            finish_error_message = typecheck_analytics_result["build_log"]
        else:
            # Validate output structure
            buffer = ProgramBuffer.from_dict(state["program_state"])
            baseline_content = self._get_baseline_content(state)
            validation_result = validate_inferrer_output(
                baseline_content,
                buffer.get_current(),
                previous_impl=state.get("previous_attempt_impl"),
            )
            if validation_result.has_error():
                build_log = validation_result.get_error()
                logger.warning(
                    f"Inferrer output validation failed: {build_log}"
                )
                final_result = {"typechecks": False, "build_log": build_log}
                typecheck_analytics_result = {
                    "typechecks": False,
                    "diagnostics": [],
                    "build_log": build_log,
                }
                finish_outcome = AttemptOutcome.VALIDATION_FAILED
                finish_error_message = build_log
            else:
                validation_passed = True
                logger.info("Output validation passed (only invariant changes, with actual changes detected)")

                raw_typecheck_result = await self._run_typecheck_step(state)
                typecheck_analytics_result = raw_typecheck_result
                final_result = dict(raw_typecheck_result)

                if raw_typecheck_result.get("typechecks"):
                    inv_result = await self._check_invariants_step(state)
                    correctness_payload = inv_result.get("correctness_analytics")
                    correctness_text = inv_result.get("correctness_analytics_text")
                    check_status = inv_result.get("check_status", CorrectnessVerdict.OK.value)
                    if check_status in {
                        CorrectnessVerdict.ISSUES.value,
                        CorrectnessVerdict.INCONCLUSIVE.value,
                    }:
                        final_result["typechecks"] = False
                        ctx = final_result.get("continuation_ctx", {})
                        final_result["continuation_ctx"] = {
                            **ctx,
                            **inv_result.get("continuation_ctx", {}),
                        }
                        finish_outcome = (
                            AttemptOutcome.CORRECTNESS_ISSUES
                            if check_status == CorrectnessVerdict.ISSUES.value
                            else AttemptOutcome.CORRECTNESS_INCONCLUSIVE
                        )
                        if correctness_text:
                            finish_error_message = correctness_text
                    else:
                        current_program = ProgramBuffer.from_dict(
                            final_result.get("program_state", state["program_state"])
                        ).get_current()
                        final_result["program_state"] = ProgramBuffer.from_dict(
                            state["program_state"]
                        ).update_current(current_program, promote_to_stable=True)
                        final_result["goal_extraction_grind_gen_param"] = inv_result.get(
                            "goal_extraction_grind_gen_param"
                        )
                else:
                    finish_outcome = self._typecheck_failure_outcome(raw_typecheck_result)
                    finish_error_message = str(raw_typecheck_result.get("build_log", ""))

        self._record_typecheck_analytics(
            state,
            validation_passed=validation_passed,
            typecheck_result=typecheck_analytics_result,
        )
        if correctness_payload is not None:
            self._record_correctness_analytics(
                state,
                correctness_payload,
                text=correctness_text,
            )
        if finish_outcome is not None:
            self._finish_attempt(
                state,
                final_outcome=finish_outcome,
                error_message=finish_error_message,
            )

        return final_result

    @DBOS.step()
    async def _run_typecheck_step(self, state: VelvetAgentState) -> dict:
        """Run typecheck and surface PBT counterexamples.

        Uses info-level diagnostics so `[velvet_plausible_test] FAIL:` messages
        are visible during invariant inference.
        """
        logger.info("Running typecheck with lake build")

        output_file = state.get("output_file", "")
        result = lean_build_file_helper(output_file, include_info_logs=True)

        counterexamples = get_pbt_counterexamples(result.diagnostics)
        if counterexamples:
            feedback = format_pbt_feedback(counterexamples)
            logger.warning(
                f"PBT found {len(counterexamples)} counterexample(s) during invariant inference"
            )
            return {
                "typechecks": False,
                "diagnostics": result.diagnostics,
                "build_log": feedback,
            }

        update_dict: dict[str, object] = {
            "typechecks": result.typechecks,
            "diagnostics": result.diagnostics,
            "build_log": result.as_string(["error"]),
        }

        if result.typechecks:
            program = Path(output_file).read_text()
            update_dict["program_state"] = ProgramBuffer.from_dict(
                state["program_state"]
            ).update_current(program)

        return update_dict

    async def _validate_goals_typecheck(
        self, state: VelvetAgentState, invariant_goals: list, non_invariant_goals: list
    ) -> Optional[str]:
        """Validate that each extracted goal's sorried version typechecks.

        Goals with malformed types (e.g. from bad invariants) won't typecheck
        even with sorry. Detecting this early avoids wasting time on mechanical
        discharge and gives targeted feedback about which invariant is broken.

        Returns feedback string if any goal fails, None if all pass.
        """
        try:
            client, _ = await self._ensure_pantograph_setup(state)
        except Exception as e:
            raise RuntimeError(f"Pantograph setup failed during goal typecheck validation: {e}") from e

        failures = []
        for goal_wrapper in invariant_goals:
            try:
                build = await client.check_build(goal_wrapper.goal.as_sorried())
            except Exception as e:
                raise RuntimeError(
                    f"Pantograph failed while typechecking invariant goal '{goal_wrapper.invariant_name}'"
                ) from e
            if not build.typechecks:
                logger.warning(
                    f"Invariant goal '{goal_wrapper.invariant_name}' does not typecheck as sorry"
                )
                failures.append(
                    f"- Invariant `{goal_wrapper.invariant_name}` "
                    f"(`{goal_wrapper.invariant_statement}`) produces a goal that does not "
                    f"typecheck even with sorry. This means the invariant itself is ill-typed.\n"
                    f"  Error: {build.as_string(['error'])}"
                )

        for goal_wrapper in non_invariant_goals:
            try:
                build = await client.check_build(goal_wrapper.goal.as_sorried())
            except Exception as e:
                raise RuntimeError(
                    f"Pantograph failed while typechecking non-invariant goal '{goal_wrapper.goal_type}'"
                ) from e
            if not build.typechecks:
                logger.warning(
                    f"Non-invariant goal '{goal_wrapper.goal_type}' does not typecheck as sorry"
                )
                failures.append(
                    f"- {goal_wrapper.goal_type.capitalize()} goal does not typecheck even "
                    f"with sorry, likely due to ill-typed invariants in its premises.\n"
                    f"  Error: {build.as_string(['error'])}"
                )

        if failures:
            return (
                "## Ill-Typed Goals\n\n"
                "The following goals do not typecheck even as sorry placeholders. "
                "The invariants that produce them are ill-typed and must be fixed.\n\n"
                + "\n".join(failures)
            )
        return None

    async def _check_invariants_step(self, state: VelvetAgentState) -> dict:
        """Check invariant strength and correctness.

        Not a @DBOS.step() — orchestrates five phases:
          1. Extract goals from the current program
          2. Validate that all goals typecheck as sorry (catch ill-typed invariants)
          3. Discharge goals mechanically (automation + MCTS)
          4. Counter-example search (plausible check)
          5. LLM correctness/strength check on remaining goals
        Inner check_goals_correctness_batch steps are independently checkpointed.
        """
        logger.info("Checking invariant strength and correctness")

        correctness_payload = InferrerCorrectnessAnalytics()

        def finish_result(
            check_status: CorrectnessVerdict,
            *,
            feedback_key: str | None = None,
            feedback_text: str | None = None,
            grind_gen_param: int | None = None,
        ) -> dict[str, Any]:
            correctness_payload.verdict = check_status
            result: dict[str, Any] = {
                "check_status": check_status.value,
                "correctness_analytics": correctness_payload,
            }
            if grind_gen_param is not None:
                result["goal_extraction_grind_gen_param"] = grind_gen_param
            if feedback_text is not None:
                result["correctness_analytics_text"] = feedback_text
            if feedback_key is not None and feedback_text is not None:
                result["continuation_ctx"] = {feedback_key: feedback_text}
            return result

        # Prepare pantograph + hint discovery up front so grindable hints can be
        # injected during goal extraction.
        try:
            await self._ensure_pantograph_setup(state)
        except Exception as e:
            logger.warning(f"Pantograph setup before extraction failed: {e}")

        # Phase 1: extract goals
        try:
            extracted = await self._extract_goals(state)
        except GoalExtractionError as e:
            err = str(e)
            logger.warning(f"Goal extraction failed - will trigger retry: {err}")
            retry_feedback = f"""This seems to have triggered an error while extracting the goals.

Please retry with simpler, more focused invariants:
- simplify invariant expressions where possible
- remove redundant invariants
- avoid overly complex quantified formulas unless essential

Also inspect the raw extraction diagnostics and apply any targeted fix they suggest (e.g., syntax issue, missing assumptions, brittle rewriting pattern, or timeout-prone proof structure).

Raw extraction diagnostics:
```
{err}
```
"""
            return finish_result(
                CorrectnessVerdict.ISSUES,
                feedback_key="Goal Extraction Feedback",
                feedback_text=retry_feedback,
            )

        if extracted is None:
            return finish_result(CorrectnessVerdict.OK)

        invariant_goals = extracted.invariant_goals
        non_invariant_goals = extracted.non_invariant_goals
        grind_gen_param = extracted.grind_gen_param
        correctness_payload.invariant_goal_count = len(invariant_goals)
        correctness_payload.non_invariant_goal_count = len(non_invariant_goals)

        manual_check_inconclusive = False
        manual_check_error = ""
        undischarged_inv = invariant_goals
        undischarged_non = non_invariant_goals

        if not invariant_goals and not non_invariant_goals:
            logger.info("No goals found - skipping check")
            return finish_result(CorrectnessVerdict.OK, grind_gen_param=grind_gen_param)

        try:
            # Phase 2: validate goals typecheck as sorry
            typecheck_feedback = await self._validate_goals_typecheck(
                state, invariant_goals, non_invariant_goals
            )
            correctness_payload.extracted_goals_typecheck_passed = typecheck_feedback is None
            if typecheck_feedback:
                logger.info("Ill-typed goals detected - will trigger retry")
                return finish_result(
                    CorrectnessVerdict.ISSUES,
                    feedback_key="Difficulty Assessment Feedback",
                    feedback_text=typecheck_feedback,
                    grind_gen_param=grind_gen_param,
                )

            # Phase 3: mechanical discharge
            undischarged_inv, undischarged_non = await self._discharge_goals(
                state, invariant_goals, non_invariant_goals
            )
            correctness_payload.automation_discharged_invariant_goals = (
                len(invariant_goals) - len(undischarged_inv)
            )
            correctness_payload.automation_discharged_non_invariant_goals = (
                len(non_invariant_goals) - len(undischarged_non)
            )
            if not undischarged_inv and not undischarged_non:
                logger.info("All goals discharged mechanically")
                return finish_result(CorrectnessVerdict.OK, grind_gen_param=grind_gen_param)

            # Phase 4: counter-example search
            inv_feedback = await self._check_plausible(state, undischarged_inv, undischarged_non)
            correctness_payload.counterexample_found = inv_feedback is not None
            if inv_feedback:
                logger.info("Counter-example detected - will trigger retry")
                retry_feedback = f"""{inv_feedback}

The automated difficulty assessment identified invariants that may be hard/impossible to prove. These invariants may not be sufficient to prove the specification/goal.

Please rethink them, potentially taking the suggestions into account. Making changes is critical - please consider the suggestions and incorporate meaningful modifications."""
                return finish_result(
                    CorrectnessVerdict.ISSUES,
                    feedback_key="Difficulty Assessment Feedback",
                    feedback_text=retry_feedback,
                    grind_gen_param=grind_gen_param,
                )
        except Exception as e:
            manual_check_inconclusive = True
            manual_check_error = str(e)
            logger.warning(f"Manual invariant checks inconclusive: {e}")

        # Phase 5: LLM fallback on remaining goals
        llm_feedback, llm_results = await self._check_goals_via_llm(
            state, undischarged_inv, undischarged_non
        )
        correctness_payload.llm_results = llm_results
        if llm_feedback:
            logger.info("LLM identified issues in remaining goals - will trigger retry")
            prefix = ""
            if manual_check_inconclusive:
                prefix = (
                    "Manual Pantograph-based checks were inconclusive due to infrastructure failure.\n\n"
                )
            retry_feedback = f"""{prefix}{llm_feedback}

The automated difficulty assessment identified invariants that may be hard/impossible to prove. These invariants may not be sufficient to prove the specification/goal.

Please rethink them, potentially taking the suggestions into account. Making changes is critical - please consider the suggestions and incorporate meaningful modifications."""
            return finish_result(
                CorrectnessVerdict.ISSUES,
                feedback_key="Difficulty Assessment Feedback",
                feedback_text=retry_feedback,
                grind_gen_param=grind_gen_param,
            )

        if manual_check_inconclusive:
            inconclusive_feedback = (
                "Manual Pantograph-based invariant checks were inconclusive due to infrastructure failure "
                f"({manual_check_error}). The LLM fallback did not find a concrete issue, but the goals "
                "were not mechanically validated. Retry invariant checking with a fresh Pantograph server."
            )
            return finish_result(
                CorrectnessVerdict.INCONCLUSIVE,
                feedback_key="Difficulty Assessment Feedback",
                feedback_text=inconclusive_feedback,
                grind_gen_param=grind_gen_param,
            )

        return finish_result(CorrectnessVerdict.OK, grind_gen_param=grind_gen_param)

    # NOTE: Step-in-step with judge.evaluate — see velvet_programmer._judge_node
    # for full rationale. Safe because post-evaluate code is trivial dict
    # construction, and removing the step would expose the file read to stale
    # disk state on replay.
    @shutdown_boundary("before inferrer judge step")
    @DBOS.step()
    async def _judge_node(self, state: VelvetAgentState) -> dict:
        """Finalize inferrer output without an external judge call.

        The invariant inferrer already performs stronger mechanical validation in
        `_typecheck_node` (goal extraction, Pantograph typecheck/discharge,
        plausible checks, and LLM fallback on remaining goals). The extra
        velvet_judge pass mostly re-checks build status and prompt compliance, so
        we bypass it here to save cost and latency.
        """
        logger.info("Bypassing judge evaluation for invariant inferrer; marking PASS")

        lean_file = LeanFile.from_path(state["output_file"])
        impl_section = lean_file.get_section("Impl", assert_exists=True)
        verdict = JudgeVerdict.PASS
        reasoning = (
            "Judge bypassed for velvet_invariant_inferrer. "
            "Mechanical invariant validation in _typecheck_node is treated as the authoritative check."
        )

        self._finish_attempt(
            state,
            final_outcome=(
                AttemptOutcome.JUDGE_PASS
                if verdict == JudgeVerdict.PASS
                else AttemptOutcome.JUDGE_FAIL
            ),
        )

        result: dict[str, Any] = {
            "judge_verdict": verdict,
            "judge_reasoning": reasoning,
            "messages": [],  # Clear messages for fresh start
        }

        if verdict == JudgeVerdict.PASS:
            program = Path(state["output_file"]).read_text()
            result["program_state"] = ProgramBuffer.from_dict(
                state["program_state"]
            ).update_current(program, promote_to_stable=True)
            result.update(self._save_phase_result(state, program))

        # Track rejections
        if verdict == JudgeVerdict.FAIL:
            rejections_dict = dict(state.get("judge_rejections", {}))
            current = rejections_dict.get(self.name, 0)
            rejections_dict[self.name] = current + 1
            result["judge_rejections"] = rejections_dict
            logger.info(f"Judge rejected {self.name} (rejection #{rejections_dict[self.name]})")

        return result

    @shutdown_boundary("before inferrer retry-after-judge step")
    @DBOS.step()
    def _setup_retry_after_judge_node(self, state: VelvetAgentState) -> dict:
        """Set up state for retry after judge rejection.

        For inferrer, also revert stable content back to programmer's stable version.
        """
        logger.info("Setting up retry after judge rejection")

        lean_file = LeanFile.from_path(state["output_file"])
        impl_section = lean_file.get_section("Impl", assert_exists=True)

        buffer = ProgramBuffer.from_dict(state["program_state"])
        result: dict = {
            "continuation_ctx": {
                "Implementation Judged by the Judge": impl_section.content
            },
        }

        # Revert stable content to programmer's version (matches old behavior)
        phase_results = state.get("phase_results", {})
        from agents.velvet_programmer import VelvetProgrammerAgent
        programmer_name = VelvetProgrammerAgent.name
        if programmer_name in phase_results:
            programmer_stable = phase_results[programmer_name].get("stable_content", "")
            if programmer_stable:
                logger.info(f"Reverted to {programmer_name}'s version")
                result["program_state"] = buffer.update_stable(programmer_stable)
                result["goal_extraction_grind_gen_param"] = None

        return result

    def _should_continue_after_typecheck(self, state: VelvetAgentState) -> str:
        """Determine whether to retry or proceed to judge."""
        logger.info(
            f"_should_continue_after_typecheck: typechecks={state['typechecks']}, attempt={state['attempt']}/{self.max_attempts}"
        )

        if state["typechecks"]:
            logger.info("✓ Program typechecks successfully - proceeding to judge")
            return "judge"
        if state["attempt"] >= self.max_attempts:
            logger.error(f"Max attempts ({self.max_attempts}) reached without success")
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=self.max_attempts,
                reason="Failed to improve invariants",
            )
        return "retry"

    def _should_continue_after_judge(self, state: VelvetAgentState) -> str:
        """Determine whether to retry after judge or finish."""
        if state.get("judge_verdict") == JudgeVerdict.PASS:
            logger.info("✓ Judge passed - finishing")
            key = f"inferrer_{state['output_file']}"
            PantographFactory.cleanup(key)
            return "done"

        rejections = state.get("judge_rejections", {}).get(self.name, 0)
        if rejections >= self.max_judge_rejections:
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=rejections,
                reason="Judge rejected too many times",
            )
        logger.info(f"↻ Judge rejected - retrying...")
        return "retry"


def main():
    """Entry point for lloom-agent-invariant-inferrer CLI command."""
    VelvetInvariantInferrerAgent.main()


def _log_impl_section_diff(old_content: str, new_content: str, *, label: str) -> None:
    """Log a labeled diff of the Impl section between two Velvet programs."""
    try:
        old_impl = (
            LeanFile.from_content(old_content)
            .get_section("Impl", assert_exists=True)
            .content
            .strip()
        )
        new_impl = (
            LeanFile.from_content(new_content)
            .get_section("Impl", assert_exists=True)
            .content
            .strip()
        )
    except Exception as e:
        logger.warning(f"Failed to compute Impl section diff for {label}: {e}")
        return

    impl_diff = Differ("old:Impl", old_impl, "new:Impl", new_impl)
    logger.info(f"Impl section diff ({label}):\n{impl_diff.format()}")


def _log_impl_text_diff(old_impl: str, new_impl: str, label: str) -> None:
    """Log a diff between two Impl-section bodies."""
    impl_diff = Differ("old:Impl", old_impl.strip(), "new:Impl", new_impl.strip())
    logger.info(f"Impl section diff ({label}):\n{impl_diff.format()}")


def _extract_annotation_lines(body: str) -> list[tuple[str, ...]]:
    """Extract while-annotation lines, ignoring blank lines and full-line `--` comments."""
    if not body:
        return []

    lines = body.splitlines()
    blocks: list[tuple[str, ...]] = []
    i = 0

    while i < len(lines):
        stripped = lines[i].strip()
        if not stripped.startswith("while "):
            i += 1
            continue

        block: list[str] = []
        if stripped.endswith(" do"):
            blocks.append(tuple())
            i += 1
            continue

        i += 1
        while i < len(lines):
            annotation_line = lines[i].strip()
            if annotation_line == "do" or annotation_line.endswith(" do"):
                i += 1
                break
            if annotation_line and not annotation_line.startswith("--"):
                if annotation_line.startswith(("invariant", "done_with", "decreasing")):
                    block.append(" ".join(annotation_line.split()))
            i += 1

        blocks.append(tuple(block))

    return blocks


def validate_inferrer_output(
    baseline_content: str,
    new_content: str,
    previous_impl: str | None = None,
) -> ValidationResult:
    """Validate output from Inferrer agent.

    Required sections: Specs, Impl, TestCases, Pbt, Assertions
    Unchanged sections: Specs, TestCases, Pbt, Assertions
    Impl section: changes only allowed within while blocks
    """
    required = ["Specs", "Impl", "TestCases", "Pbt", "Assertions"]
    unchanged = ["Specs", "TestCases", "Pbt", "Assertions"]

    try:
        old_file = LeanFile.from_content(baseline_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse old content as LeanFile: {e}")

    try:
        new_file = LeanFile.from_content(new_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse new content as LeanFile: {e}")

    # Always log the baseline-vs-new Impl diff for debugging.
    _log_impl_section_diff(
        baseline_content,
        new_content,
        label="baseline -> new attempt",
    )
    if previous_impl is not None:
        try:
            new_impl_for_log = (
                new_file.get_section("Impl", assert_exists=True).content.strip()
            )
            _log_impl_text_diff(
                previous_impl,
                new_impl_for_log,
                label="previous attempt -> new attempt",
            )
        except Exception as e:
            logger.warning(
                f"Failed to compute previous-attempt Impl diff inside validation: {e}"
            )

    # Check required sections exist
    missing = [s for s in required if not new_file.has_section(s)]
    if missing:
        return ValidationResult.error(
            f"Inferrer output missing required sections: {missing}\n"
            f"Found sections: {new_file.section_names()}"
        )

    # Check unchanged sections
    for section_name in unchanged:
        if not old_file.has_section(section_name):
            return ValidationResult.error(
                f"Inferrer input missing section '{section_name}' that should be unchanged"
            )

        d = Differ(
            f"old:{section_name}",
            old_file.get_section(section_name, assert_exists=True).content.strip(),
            f"new:{section_name}",
            new_file.get_section(section_name, assert_exists=True).content.strip(),
        )
        if not d.is_empty():
            return ValidationResult.error(
                f"Inferrer modified section '{section_name}' which should be unchanged.\n"
                f"Diff:\n{d.format()}"
            )

    # Validate Impl section using structured comparison
    old_impl = old_file.get_section("Impl", assert_exists=True).content.strip()
    new_impl = new_file.get_section("Impl", assert_exists=True).content.strip()

    try:
        old_method = get_velvet_method(old_impl)
    except Exception as e:
        return ValidationResult.error(f"Failed to parse old Impl as VelvetMethod: {e}")

    try:
        new_method = get_velvet_method(new_impl)
    except Exception as e:
        return ValidationResult.error(f"Failed to parse new Impl as VelvetMethod: {e}")

    # Verify method signature unchanged
    if old_method.name != new_method.name:
        return ValidationResult.error(
            f"Method name changed: '{old_method.name}' -> '{new_method.name}'"
        )

    if old_method.params != new_method.params:
        return ValidationResult.error(
            f"Method params changed:\n  old: {old_method.params}\n  new: {new_method.params}"
        )

    if old_method.returns != new_method.returns:
        return ValidationResult.error(
            f"Method returns changed:\n  old: {old_method.returns}\n  new: {new_method.returns}"
        )

    if old_method.requires != new_method.requires:
        return ValidationResult.error(
            f"Method requires changed:\n  old: {old_method.requires}\n  new: {new_method.requires}"
        )

    if old_method.ensures != new_method.ensures:
        return ValidationResult.error(
            f"Method ensures changed:\n  old: {old_method.ensures}\n  new: {new_method.ensures}"
        )

    # Verify only annotations changed by normalizing bodies and comparing
    # normalize_body_with_while_tags strips annotations, keeps everything else tagged
    old_normalized = normalize_body_with_while_tags(old_method.body or "")
    new_normalized = normalize_body_with_while_tags(new_method.body or "")

    d = Differ("old:body", old_normalized, "new:body", new_normalized)
    if not d.is_empty():
        return ValidationResult.error(
            f"Changes detected outside while loop annotations.\n"
            f"Only invariant/done_with/decreasing lines can be modified.\n"
            f"Diff:\n{Differ('old:impl', old_impl, 'new:impl', new_impl).format()}"
        )

    # Check if there are actual changes in the Impl section
    impl_diff = Differ("old:impl", old_impl, "new:impl", new_impl)
    if impl_diff.is_empty():
        return ValidationResult.error(
            "Detected no changes in the program, please try again and make the changes taking the current suggestions and feedback into account"
        )

    if previous_impl is not None:
        try:
            previous_method = get_velvet_method(previous_impl)
        except Exception as e:
            return ValidationResult.error(
                f"Failed to parse previous inferrer Impl for comparison: {e}"
            )

        previous_impl_diff = Differ("previous:impl", previous_impl, "new:impl", new_impl)
        if previous_impl_diff.is_empty():
            return ValidationResult.error(
                "Detected no changes relative to the previous attempt. Please make a substantive annotation change."
            )

        previous_annotations = _extract_annotation_lines(previous_method.body or "")
        new_annotations = _extract_annotation_lines(new_method.body or "")
        if previous_annotations == new_annotations:
            return ValidationResult.error(
                "Detected only comment/whitespace changes relative to the previous attempt. "
                "Please change at least one invariant/done_with/decreasing line."
            )

    return ValidationResult.ok()


if __name__ == "__main__":
    main()
