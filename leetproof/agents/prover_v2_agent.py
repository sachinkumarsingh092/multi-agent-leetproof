"""ProverV2Agent — tool-driven proof agent.

Replaces the fixed shallow-solve → decomposition pipeline with a bounded
tool loop where the LLM decides what to do. The workflow owns recursion;
the LLM owns strategy within a single goal.
"""

from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from dbos import DBOS
from langchain_core.messages import (
    AIMessage,
    BaseMessage,
    HumanMessage,
    ToolMessage,
)
from langchain_core.tools import tool
from langgraph.graph import StateGraph

from agents.base import BaseAgent
from utils.lean.parser import LeanFile
from utils.message_constants import AGENT_PROMPT
from utils.message_helpers import (
    PromptSegment,
    bullets,
    create_prompt,
    log_llm_interaction,
    render_prompt,
    section,
    stable,
)
from utils.proof_types import (
    DecompositionResult,
    DonePayload,
    DoneSignal,
    FailureInfo,
    LemmaRegistration,
    ProofResult,
    ProofSubmission,
    ProveGoalV2State,
    ProvingContext,
    SketchSubmission,
    SubgoalInfo,
    SubgoalOutcome,
)
from utils.token_tracker import set_current_agent

if TYPE_CHECKING:
    from agents.proof_reasoning_agent import ProofReasoningAgent
    from agents.prover_agent import ProverAgent
    from agents.retriever_agent import RetrieverAgent
    from providers import LLMConfig, ReasoningLevel

logger = logging.getLogger(__name__)

PROVE_GOAL_V2_LARGE_PROOF_LINE_THRESHOLD = 35
PROVE_GOAL_V2_DECOMPOSITION_HINT_FAILURE_THRESHOLD = 3
PROVE_GOAL_V2_DEFAULT_MAX_ITERATIONS = 20
PROVE_GOAL_V2_MAX_GET_REASONING_CALLS = 3
PROVE_GOAL_V2_MAX_LEAN_EXPLORE_CALLS = 5
PROVE_GOAL_V2_DEFAULT_RESULTS_PER_QUERY = 3

# Placeholder — will be replaced with a real prompt later.
from prompts.prompts import PROVE_GOAL_V2_SYSTEM


@DBOS.dbos_class()
class ProverV2Agent(BaseAgent):
    """Tool-driven proof agent.

    The LLM gets tools to validate proofs, validate sketches, search for
    lemmas, get reasoning help, and register helper lemmas. It drives the
    proving process and signals when it's done.
    """

    name = "prover_v2"
    description = "Tool-driven Lean proof agent"
    system_prompt = ""  # Not used — uses _v2_build_system_prompt

    def __init__(
        self,
        config: LLMConfig,
        *,
        prover: ProverAgent,
        retriever: RetrieverAgent,
        reasoning: ProofReasoningAgent,
        default_max_iterations: int = PROVE_GOAL_V2_DEFAULT_MAX_ITERATIONS,
        max_lean_explore_calls: int = PROVE_GOAL_V2_MAX_LEAN_EXPLORE_CALLS,
        lean_explore_results_per_query: int = PROVE_GOAL_V2_DEFAULT_RESULTS_PER_QUERY,
        config_name: str | None = None,
        reasoning_level: ReasoningLevel | None = None,
    ):
        self._prover = prover
        self._retriever = retriever
        self._reasoning = reasoning
        self._default_max_iterations = default_max_iterations
        self._max_lean_explore_calls = max_lean_explore_calls
        self._lean_explore_results_per_query = lean_explore_results_per_query
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    def build_graph(self) -> StateGraph:
        raise NotImplementedError("ProverV2Agent doesn't use graph-based workflow")

    async def run_workflow(self, state: dict) -> dict:
        raise NotImplementedError("Use prove() directly")

    @staticmethod
    def _log_tool_submission(label: str, content: str) -> None:
        """Log a multiline tool submission payload."""
        logger.info(f"{label}:\n{'-' * 80}\n{content}\n{'-' * 80}")

    @staticmethod
    def _active_lemma_blocks(state: ProveGoalV2State) -> list[str]:
        return [lemma.proof for lemma in state.active_lemmas]

    async def _load_pending_lemmas(self, ctx: ProvingContext) -> None:
        """Replay pending helper lemmas into pantograph if needed."""
        from utils.lean.parser import LeanFile

        lemma_blocks = [block.strip() for block in ctx.pending_lemma_blocks if block.strip()]
        if not lemma_blocks:
            return

        pantograph = self._prover._get_pantograph(ctx)
        loaded_section_content: str | None = None
        for block in lemma_blocks:
            try:
                await pantograph.load_definitions(ctx.pantograph.key, block)
            except Exception as e:
                if loaded_section_content is None:
                    lean_file = LeanFile.from_content(ctx.read_file())
                    loaded_section_content = "\n\n".join(
                        lean_file.get_section(section, assert_exists=True).full_text()
                        for section in ctx.sections
                    )
                logger.warning(
                    "prove_goalv2: pending lemma replay failed for %s: %s\n"
                    "Pending lemma block:\n%s",
                    ctx.goal_name,
                    e,
                    block,
                )
                if block in loaded_section_content:
                    logger.info(
                        "prove_goalv2: pending lemma block for %s already exists in loaded sections; ignoring replay failure",
                        ctx.goal_name,
                    )
                    continue
                raise

    async def _prepare_context(self, ctx: ProvingContext) -> ProvingContext:
        """Ensure hints are discovered and sections are loaded into Pantograph."""
        if ctx.hint_sections and not ctx.proof_hints:
            proof_hints = await self._prover._discover_hints(ctx)
            logger.info("Discovered proof hints for prover_v2:\n%s", proof_hints)
            ctx = ctx.copy_with()
            ctx.proof_hints = proof_hints

        await self._prover.load_sections_on_pantograph(ctx, ctx.sections)
        await self._load_pending_lemmas(ctx)
        return ctx

    async def _depth_failure(
        self,
        ctx: ProvingContext,
        *,
        depth: int,
        max_depth: int,
    ) -> ProofResult:
        return await self._prover._fail_with_sorried_goal(
            ctx,
            error=f"Max depth {max_depth} reached",
            failures=[FailureInfo(
                phase="prove_goalv2",
                goal_name=ctx.goal_name,
                depth=depth,
                error=f"Max depth {max_depth} reached",
            )],
        )

    async def _try_automation_result(
        self,
        ctx: ProvingContext,
    ) -> ProofResult | None:
        """Try the cheap automation path before invoking the LLM."""
        automation_result = await self._prover._try_automation(ctx)
        if not automation_result.success:
            return None
        return await self._prover._finalize_result(
            ctx,
            ProofResult(
                success=True,
                content="",
                proof=automation_result.proof,
                lemmas=ctx.pending_lemma_blocks,
            ),
        )

    def _initial_messages(self, ctx: ProvingContext) -> list[BaseMessage]:
        """Build the initial system + user messages for a goal."""
        return [
            self.create_system_message(
                content=self._v2_build_system_prompt(ctx),
                message_type=AGENT_PROMPT,
            ),
            HumanMessage(content=self._v2_build_user_message(ctx)),
        ]

    def _tool_limits(self, ctx: ProvingContext) -> dict[str, int]:
        """Per-goal tool budgets shown to the LLM and enforced in the loop."""
        return {
            "get_reasoning": PROVE_GOAL_V2_MAX_GET_REASONING_CALLS,
            "lean_explore_search": self._max_lean_explore_calls,
            "check_theorem": ctx.attempt_budgets.shallow.max_attempts,
            "decompose_goal": ctx.attempt_budgets.decomposition.max_attempts,
        }

    def _tool_budget_summary(self, ctx: ProvingContext) -> str:
        """Render the per-goal tool budget summary for the user prompt."""
        limits = self._tool_limits(ctx)
        return (
            "## Tool Budgets\n\n"
            f"- `get_reasoning`: {limits['get_reasoning']} calls\n"
            f"- `lean_explore_search`: {limits['lean_explore_search']} calls\n"
            f"- `check_theorem`: {limits['check_theorem']} attempts\n"
            f"- `decompose_goal`: {limits['decompose_goal']} attempts\n\n"
            "Tool responses will tell you how many uses remain. Use them carefully."
        )

    def _depth_guidance(self, *, depth: int, max_depth: int) -> str:
        lines = [
            "## Goal Depth",
            "",
            f"You are at depth {depth}/{max_depth}.",
        ]
        if depth >= max_depth:
            lines.extend([
                "Further decomposition is not allowed for this goal.",
                "Do not call `decompose_goal`. Focus on solving the current goal directly with your remaining `check_theorem`, `lean_explore_search`, `get_reasoning`, and `register_lemmas` budget.",
                "If those direct attempts are exhausted and no useful progress remains, call `done(\"stuck\")`.",
            ])
        return "\n".join(lines)

    # ── Workflow entry point ─────────────────────────────────────

    @DBOS.workflow()
    async def prove(
        self,
        ctx: ProvingContext,
        max_depth: int = 4,
        max_iterations: int | None = None,
    ) -> ProofResult:
        """Tool-driven proof workflow matching ProverAgent's public interface."""
        return await self._prove_goal(
            ctx,
            depth=1,
            max_depth=max_depth,
            max_iterations=max_iterations or self._default_max_iterations,
        )

    def write_shutdown_snapshot(
        self,
        ctx: ProvingContext,
        *,
        extra_lemma_blocks: list[str] | None = None,
    ) -> str:
        """Delegate shutdown snapshots to the underlying file-finalizing prover."""
        return self._prover.write_shutdown_snapshot(
            ctx,
            extra_lemma_blocks=extra_lemma_blocks,
        )

    def write_decomposition_shutdown_snapshot(
        self,
        ctx: ProvingContext,
        *,
        subgoals: list[SubgoalInfo],
        assembled_sketch: str,
        extra_lemma_blocks: list[str] | None = None,
    ) -> str:
        """Delegate decomposition shutdown snapshots to the underlying prover."""
        return self._prover.write_decomposition_shutdown_snapshot(
            ctx,
            subgoals=subgoals,
            assembled_sketch=assembled_sketch,
            extra_lemma_blocks=extra_lemma_blocks,
        )

    async def _prove_goal(
        self,
        ctx: ProvingContext,
        depth: int = 1,
        max_depth: int = 4,
        max_iterations: int | None = None,
    ) -> ProofResult:
        """Internal tool-driven proof workflow. LLM chooses strategy via tool calls."""
        set_current_agent(self.name)
        max_iterations = max_iterations or self._default_max_iterations

        ctx = await self._prepare_context(ctx)
        if depth > max_depth:
            return await self._depth_failure(ctx, depth=depth, max_depth=max_depth)

        automation_result = await self._try_automation_result(ctx)
        if automation_result is not None:
            return automation_result

        from utils.shutdown import shutdown_hook, ShutdownHookMode

        state = ProveGoalV2State(max_iterations=max_iterations)
        tool_schemas, tool_fns = self._build_tools(
            ctx,
            state,
            depth=depth,
            max_depth=max_depth,
        )
        messages = self._initial_messages(ctx)
        messages.append(HumanMessage(content=self._depth_guidance(depth=depth, max_depth=max_depth)))

        with shutdown_hook(
            ShutdownHookMode.PUSH,
            lambda: self.write_shutdown_snapshot(
                ctx,
                extra_lemma_blocks=self._active_lemma_blocks(state),
            ),
        ):
            try:
                await self._tool_loop(messages, tool_schemas, tool_fns, state)
            except DoneSignal as sig:
                state.done_payload = sig.payload

            return await self._finalize(ctx, state, depth, max_depth)

    # ── Tool loop ────────────────────────────────────────────────

    async def _dispatch_tool(self, tool_call, tool_fns: dict) -> str:
        """Execute a tool call directly, bypassing LangChain's ainvoke."""
        tool_name = tool_call["name"]
        tool_args = tool_call["args"]

        logger.info(f"→ {tool_name}")

        fn = tool_fns.get(tool_name)
        if fn is None:
            logger.warning(f"Tool not found: {tool_name}")
            return f"Tool not found: {tool_name}"

        try:
            result = await fn(**tool_args)
            return str(result)
        except DoneSignal:
            raise  # Must propagate — this is how done() exits the loop
        except Exception as e:
            error_msg = f"Error executing tool: {e}"
            logger.error(f"Tool {tool_name} failed: {e}")
            return error_msg

    @DBOS.step()
    async def _llm_call(
        self,
        llm_with_tools,
        messages: list[BaseMessage],
        tools: list,
    ) -> BaseMessage:
        """Single LLM call — cached on DBOS replay."""
        set_current_agent(self.name)
        response = await self._invoke_llm_with_retry(
            llm_with_tools, messages, tools,
            max_retries=5, base_delay=1.0,
        )
        log_llm_interaction(self.name, messages, response)
        return response

    async def _tool_loop(
        self,
        messages: list[BaseMessage],
        tool_schemas: list,
        tool_fns: dict,
        state: ProveGoalV2State,
    ) -> None:
        """Bounded tool iteration. Raises DoneSignal when done() is called."""
        llm = self._resolve_llm()
        llm_with_tools = llm.bind_tools(tool_schemas)

        for iteration in range(state.max_iterations):
            state.iteration = iteration
            # Check for shutdown between iterations
            from utils.shutdown import handle_shutdown_if_requested
            handle_shutdown_if_requested(f"prove_goalv2 tool loop iteration {iteration}")

            # LLM call (DBOS step — cached on replay)
            response = await self._llm_call(llm_with_tools, messages, tool_schemas)
            self._log_llm_response(response, iteration)
            self._request_shutdown_for_pending_limit_breach()

            # No tool calls → nudge LLM to use tools instead of bare text
            if not (isinstance(response, AIMessage) and response.tool_calls):
                logger.warning(
                    "prove_goalv2: assistant response had no parsed tool calls; discarding and retrying "
                    "(iteration=%s)",
                    iteration,
                )
                messages.append(HumanMessage(
                    content=render_prompt(create_prompt(
                        task=stable("You must use tool calls to interact — do not output bare text."),
                        instructions=bullets([
                            "To submit a proof, call `check_theorem`.",
                            "To submit a decomposition with sorry'd subgoals, call `decompose_goal`.",
                            "To search for relevant lemmas, call `lean_explore_search`.",
                            "To get a proof plan, call `get_reasoning`.",
                            "To register a helper lemma(s), call `register_lemmas`.",
                            "To signal completion, call `done`.",
                        ], segment=PromptSegment.STABLE),
                    )).full_text()
                ))
                continue

            messages.append(response)

            # Execute each tool call — may raise DoneSignal
            for tool_call in response.tool_calls:
                try:
                    tool_result = await self._dispatch_tool(tool_call, tool_fns)
                except DoneSignal as sig:
                    messages.append(ToolMessage(
                        content=f"Accepted done({sig.payload.outcome}).",
                        tool_call_id=tool_call["id"],
                        name=tool_call["name"],
                    ))
                    raise sig
                messages.append(ToolMessage(
                    content=tool_result,
                    tool_call_id=tool_call["id"],
                    name=tool_call["name"],
                ))

        logger.warning(f"prove_goalv2: max iterations ({state.max_iterations}) reached")

    # ── Tool closures ────────────────────────────────────────────

    def _build_tools(
        self,
        ctx: ProvingContext,
        state: ProveGoalV2State,
        *,
        depth: int,
        max_depth: int,
    ) -> tuple[list, dict]:
        """Build tool closures that call DBOS steps and journal results.

        Returns:
            (tool_schemas, tool_fns) — tool_schemas for bind_tools(),
            tool_fns maps name → raw async callable for direct execution.
        """

        def _turns_note() -> str:
            """Return a turns-remaining reminder when ≤5 turns left, else empty."""
            left = state.turns_left
            if left <= 5:
                return f"\n{left} turn{'s' if left != 1 else ''} remaining."
            return ""

        def _proof_body_line_count(proof: str) -> int:
            """Count non-comment lines in the proof body after `:= ... by`."""
            import re

            parts = re.split(r":=.*?\bby\b", proof, maxsplit=1, flags=re.DOTALL)
            body = parts[1] if len(parts) == 2 else proof
            return sum(
                1
                for line in body.splitlines()
                if (stripped := line.strip()) and not stripped.startswith("--")
            )

        tool_limits = self._tool_limits(ctx)
        tool_nouns = {
            "get_reasoning": "calls",
            "lean_explore_search": "calls",
            "check_theorem": "attempts",
            "decompose_goal": "attempts",
        }
        tool_usage = {
            "get_reasoning": lambda: state.get_reasoning_calls,
            "lean_explore_search": lambda: state.lean_explore_calls,
            "check_theorem": lambda: len(state.proofs),
            "decompose_goal": lambda: len(state.sketches),
        }

        def _tool_remaining(tool_name: str) -> int:
            return max(0, tool_limits[tool_name] - tool_usage[tool_name]())

        def _budget_note(tool_name: str) -> str:
            noun = tool_nouns[tool_name]
            remaining = _tool_remaining(tool_name)
            return f"\n{tool_name} {noun} left for this goal: {remaining}. Use them carefully."

        def _tool_result(tool_name: str, message: str) -> str:
            return f"{message}{_budget_note(tool_name)}{_turns_note()}"

        def _budget_exhausted(tool_name: str) -> str | None:
            if _tool_remaining(tool_name) > 0:
                return None
            return _tool_result(tool_name, f"{tool_name} budget exhausted for this goal.")

        def _check_theorem_hints(proof: str) -> str:
            proof_lines = _proof_body_line_count(proof)
            failed_proof_count = sum(1 for p in state.proofs if not p.typechecks)
            hints: list[str] = []

            if proof_lines >= PROVE_GOAL_V2_LARGE_PROOF_LINE_THRESHOLD:
                hints.append(
                    "This proof is getting quite large. Consider breaking out a helper lemma "
                    "so you can focus on one part in isolation — it is often better for readability "
                    "and performance."
                )
            if (
                failed_proof_count >= PROVE_GOAL_V2_DECOMPOSITION_HINT_FAILURE_THRESHOLD
                and state.best_sketch is None
            ):
                hints.append(
                    "You have had several failed direct proof attempts. If the remaining difficulty "
                    "comes from a few separable intermediate obligations, try `decompose_goal` with a "
                    "small number of named `have ... := by sorry` subgoals."
                )
            if not hints:
                return ""
            return "\n\n" + "\n\n".join(hints)

        async def check_theorem(proof: str) -> str:
            """Submit a complete proof (no sorry) for validation.

            Returns typecheck result with error diagnostics if it fails.
            """
            if exhausted := _budget_exhausted("check_theorem"):
                return exhausted

            self._log_tool_submission(
                f"prove_goalv2.check_theorem submission for {ctx.goal_name}",
                proof,
            )
            submission = await self._check_theorem(ctx, proof)
            state.proofs.append(submission)

            if submission.typechecks:
                logger.info(
                    f"prove_goalv2.check_theorem accepted for {ctx.goal_name}"
                )
                return _tool_result(
                    "check_theorem",
                    f"PROOF ACCEPTED — `{ctx.goal_name}` typechecks successfully. "
                    f"Call `done(\"proved\")` to finish.",
                )

            logger.info(
                f"prove_goalv2.check_theorem rejected for {ctx.goal_name}:\n"
                f"{submission.build_result.as_string(['error'])}"
            )
            return _tool_result(
                "check_theorem",
                "PROOF FAILED.\n\n"
                f"{submission.build_result.as_string(['error'])}"
                f"{_check_theorem_hints(proof)}",
            )

        async def decompose_goal(sketch: str) -> str:
            """Submit a proof sketch (with sorry'd subgoals) for validation.

            Returns whether the sketch typechecks and what subgoals were extracted.
            """
            if depth >= max_depth:
                return _tool_result(
                    "decompose_goal",
                    "decompose_goal unavailable: this goal is already at max recursion depth "
                    f"({depth}/{max_depth}), so further decomposition is not allowed. "
                    "Focus on direct proof attempts, helper lemmas, and search with your remaining budget.",
                )
            if exhausted := _budget_exhausted("decompose_goal"):
                return exhausted

            self._log_tool_submission(
                f"prove_goalv2.decompose_goal submission for {ctx.goal_name}",
                sketch,
            )
            submission = await self._check_sketch(ctx, sketch)
            state.sketches.append(submission)

            if not submission.typechecks:
                logger.info(
                    f"prove_goalv2.decompose_goal failed typecheck for {ctx.goal_name}:\n"
                    f"{submission.build_result.as_string(['error'])}"
                )
                return _tool_result(
                    "decompose_goal",
                    "DECOMPOSITION FAILED TYPECHECK.\n\n"
                    f"{submission.build_result.as_string(['error'])}",
                )

            if submission.error:
                logger.info(
                    f"prove_goalv2.decompose_goal found incorrect subgoals for {ctx.goal_name}:\n"
                    f"{submission.error}"
                )
                return _tool_result(
                    "decompose_goal",
                    f"DECOMPOSITION TYPECHECKS but has issues:\n{submission.error}",
                )

            goals_desc = "\n".join(
                f"  {i+1}. `{sg.name}`: {sg.statement}"
                for i, sg in enumerate(submission.subgoals)
            )
            logger.info(
                f"prove_goalv2.decompose_goal accepted for {ctx.goal_name} with "
                f"{len(submission.subgoals)} subgoal(s)"
            )
            return _tool_result(
                "decompose_goal",
                f"DECOMPOSITION ACCEPTED — `{ctx.goal_name}` decomposes into "
                f"{len(submission.subgoals)} subgoal(s):\n{goals_desc}\n\n"
                f"Each subgoal will be proved recursively. "
                f"Call `done(\"decompose\")` to finish.",
            )

        async def lean_explore_search(
            queries: list[str],
            num_results_per_query: int = self._lean_explore_results_per_query,
        ) -> str:
            """Search for Lean lemmas/theorems by natural-language description.

            Each query should be short (under 15 words). Returns exact
            declaration names and signatures.
            """
            if exhausted := _budget_exhausted("lean_explore_search"):
                return exhausted

            state.lean_explore_calls += 1
            result = await self._lean_explore_search(
                queries=queries,
                num_results_per_query=num_results_per_query,
            )
            return _tool_result("lean_explore_search", f"{result}\n")

        async def get_reasoning(goal_text: str) -> str:
            """Get informal mathematical reasoning for how to prove a goal.

            Pass the theorem statement. Returns a step-by-step natural-language
            proof plan.
            """
            if exhausted := _budget_exhausted("get_reasoning"):
                return exhausted

            state.get_reasoning_calls += 1
            result = await self._get_reasoning(
                goal_theorem=goal_text,
                relevant_context=ctx.get_relevant_context(),
            )
            return _tool_result("get_reasoning", f"{result}\n")

        async def register_lemmas(proof: str) -> str:
            """Register a single proved helper lemma from a Lean code block."""
            self._log_tool_submission(
                f"prove_goalv2.register_lemmas submission for {ctx.goal_name}",
                proof,
            )

            reg = await self._register_lemma(ctx, proof)
            state.lemmas.append(reg)

            if reg.active:
                logger.info(
                    f"prove_goalv2.register_lemmas accepted declaration {reg.name} for {ctx.goal_name}"
                )
                return f"Helper lemma(s) `{reg.name}` registered and loaded.{_turns_note()}"

            logger.info(
                f"prove_goalv2.register_lemmas rejected declaration {reg.name or '<unknown>'} for {ctx.goal_name}\n{reg.error}"
            )
            label = f"`{reg.name}`" if reg.name else "helper lemma"
            return f"{label} failed to register.{_turns_note()}\n\n{reg.error}"

        async def done(
            outcome: str,
            note: str = "",
        ) -> str:
            """Signal that you are done with this goal.

            outcome must be one of:
            - "proved": A check_theorem call already succeeded.
            - "decompose": A decompose_goal call succeeded; subgoals will be proved recursively.
            - "stuck": No more useful moves.
            """
            if outcome not in ("proved", "decompose", "stuck"):
                return f"Invalid outcome '{outcome}'. Must be 'proved', 'decompose', or 'stuck'."
            payload = DonePayload(outcome=outcome, note=note)
            logger.info(
                "prove_goalv2.done called for %s:\n"
                "----------------------------------------\n"
                "outcome: %s\n"
                "turns_left: %s\n"
                "note:\n%s\n"
                "----------------------------------------",
                ctx.goal_name,
                payload.outcome,
                state.turns_left,
                payload.note or "<empty>",
            )
            if outcome == "stuck" and state.turns_left > 5 and state.stuck_done_requests == 0:
                state.stuck_done_requests += 1
                return render_prompt(create_prompt(
                    task=stable("Do not give up yet."),
                    sections=(
                        section("Stuck Note", stable(payload.note or "No note provided.")),
                    ),
                    instructions=bullets([
                        f"There are still {state.turns_left} iterations left in this goal.",
                        "You still have time to search for lemmas, register helper lemmas, or decompose the goal into subgoals.",
                        "Prefer trying `decompose_goal` if the proof naturally breaks into intermediate claims.",
                        "If you are truly stuck after another serious attempt, you may call `done(\"stuck\")` again.",
                    ], segment=PromptSegment.STABLE),
                )).full_text()
            raise DoneSignal(payload)

        tool_functions = (
            check_theorem,
            decompose_goal,
            lean_explore_search,
            get_reasoning,
            register_lemmas,
            done,
        )
        tool_fns = {fn.__name__: fn for fn in tool_functions}
        tool_schemas = [tool(fn) for fn in tool_functions]

        return tool_schemas, tool_fns

    # ── Core logic ─────────────────────────────────────────────

    async def _check_theorem(
        self,
        ctx: ProvingContext,
        proof: str,
    ) -> ProofSubmission:
        """Validate a full proof: signature check → sorry check → typecheck."""
        from utils.lean.types import LakeBuildResult, LeanDiagnostic

        # 1. Signature check
        sig_error = self._prover._validate_theorem_signature(proof, ctx)
        if sig_error:
            diag = LeanDiagnostic(severity="error", message=sig_error, line=0, column=0)
            return ProofSubmission(
                proof=proof,
                build_result=LakeBuildResult(typechecks=False, diagnostics=[diag]),
            )

        # 2. Sorry check
        if "sorry" in proof or "admit" in proof:
            diag = LeanDiagnostic(
                severity="error",
                message="Proof contains `sorry`/`admit`, this is not allowed. A complete proof is required.",
                line=0, column=0,
            )
            return ProofSubmission(
                proof=proof,
                build_result=LakeBuildResult(typechecks=False, diagnostics=[diag]),
            )

        # 3. Typecheck
        pantograph = self._prover._get_pantograph(ctx)
        build_result = await pantograph.check_build(proof)

        # 4. If success, do NOT load into context — only register_lemmas does that

        return ProofSubmission(proof=proof, build_result=build_result)

    async def _check_sketch(
        self,
        ctx: ProvingContext,
        sketch: str,
    ) -> SketchSubmission:
        """Validate a proof sketch: signature → typecheck → extract subgoals → correctness check."""
        from utils.lean.types import LakeBuildResult, LeanDiagnostic

        # 1. Signature check
        sig_error = self._prover._validate_theorem_signature(sketch, ctx)
        if sig_error:
            diag = LeanDiagnostic(severity="error", message=sig_error, line=0, column=0)
            return SketchSubmission(
                sketch=sketch,
                build_result=LakeBuildResult(typechecks=False, diagnostics=[diag]),
            )

        # 2. Typecheck the sketch (with sorries)
        build_result = await self._prover._typecheck_sketch(ctx, sketch)
        if not build_result.typechecks:
            return SketchSubmission(sketch=sketch, build_result=build_result)

        # 3. Extract subgoals
        decomp: DecompositionResult = await self._prover._extract_subgoals_from_sketch(ctx, sketch)
        if not decomp.success:
            return SketchSubmission(
                sketch=sketch,
                build_result=build_result,
                error=decomp.error or "Subgoal extraction failed",
            )

        # 4. Batch correctness check on extracted subgoals
        correctness_error = await self._check_subgoal_correctness(ctx, decomp.subgoals)

        return SketchSubmission(
            sketch=sketch,
            build_result=build_result,
            subgoals=decomp.subgoals,
            assembled_sketch=decomp.assembled_sketch,
            error=correctness_error,
        )

    async def _check_subgoal_correctness(
        self,
        ctx: ProvingContext,
        subgoals: list[SubgoalInfo],
    ) -> str:
        """Batch-check subgoal correctness. Returns error string or empty if all OK."""
        if not subgoals:
            return ""

        from agents.proof_reasoning_agent import GoalCheckInput

        goal_inputs = [
            GoalCheckInput(goal_id=sg.name, goal_statement=sg.statement)
            for sg in subgoals
        ]

        file_context = ctx.get_relevant_context()
        shared_ctx: dict[str, str] = {"File Context": file_context}
        hints = ctx.proof_hints.format_hints() if ctx.proof_hints else ""
        if hints:
            shared_ctx["Available Lemmas and Hints"] = hints

        check_results = await self._reasoning.check_goals_correctness_batch(
            goals=goal_inputs,
            shared_context=shared_ctx,
        )

        invalid_parts = []
        for sg, result in zip(subgoals, check_results):
            if not result.is_provable:
                invalid_parts.append(
                    f"Subgoal `{sg.name}`:\n{sg.statement}\n"
                    f"Reason: {result.justification or 'No justification'}\n"
                    f"Hint: {result.correction_hint or ''}"
                )

        if invalid_parts:
            error_message = f"{len(invalid_parts)} MATHEMATICALLY INCORRECT/UNPROVABLE SUBGOAL(S):\n\n" + "\n\n".join(invalid_parts)
            logger.warning(error_message)
            return error_message

        return ""

    @DBOS.step()
    async def _lean_explore_search(
        self,
        queries: list[str],
        num_results_per_query: int = PROVE_GOAL_V2_DEFAULT_RESULTS_PER_QUERY,
    ) -> str:
        """Run LeanExplore semantic search. Returns formatted string for LLM."""
        from agents.retriever_agent import SemanticSearchSpec
        from utils.lean_explore_service import DEFAULT_LEANEXPLORE_PACKAGES

        specs = [
            SemanticSearchSpec(query=q.strip(), num_results=num_results_per_query)
            for q in queries if q.strip()
        ]
        formatted, _ = await self._retriever.execute_semantic_queries(
            specs,
            package_filters=tuple(DEFAULT_LEANEXPLORE_PACKAGES),
        )
        return formatted or "No results found."

    @DBOS.step()
    async def _get_reasoning(
        self,
        goal_theorem: str,
        relevant_context: str,
    ) -> str:
        """Generate informal reasoning. Returns the reasoning text."""
        result = await self._reasoning.generate_informal_reasoning(
            goal_theorem=goal_theorem,
            relevant_context=relevant_context,
        )
        return result.informal_reasoning

    @DBOS.step()
    async def _register_lemma(
        self,
        ctx: ProvingContext,
        proof: str,
    ) -> LemmaRegistration:
        """Typecheck one helper lemma block and load it into pantograph context."""

        from utils.lean.types import LakeBuildResult, LeanDiagnostic
        if "sorry" in proof or "admit" in proof:
            diag = LeanDiagnostic(
                severity="error",
                message="Proof contains `sorry`/`admit`, this is not allowed. A complete proof is required.",
                line=0, column=0,
            )
            return LemmaRegistration(
                name="",
                proof=proof,
                active=False,
                error=(LakeBuildResult(typechecks=False, diagnostics=[diag]).as_string(["error"])),
            )

        pantograph = self._prover._get_pantograph(ctx)
        build_result = await pantograph.check_build(proof)

        if not build_result.typechecks:
            return LemmaRegistration(
                name="",
                proof=proof,
                active=False,
                error=build_result.as_string(["error"]),
            )

        try:
            build_res, new_constants = await pantograph.load_and_discover_constants(ctx.goal_name, proof)
            if build_res is not None and not build_res.typechecks:
                return LemmaRegistration(
                    name="",
                    proof=proof,
                    active=False,
                    error=f"""
The entire proof script failed to typecheck(partial typecheck isn't allowed).
If everything typechecks, then only, it's loaded to the environment.\n

*ERROR*:
{build_res.as_string(['error'])}
"""
                )
            return LemmaRegistration(
                name=",".join(new_constants),
                proof=proof,
                active=True,
            )
        except Exception as e:
            return LemmaRegistration(
                name="",
                proof=proof,
                active=False,
                error=f"Helper lemma loading failed: {e}",
            )


    # ── Finalize ─────────────────────────────────────────────────

    async def _finalize(
        self,
        ctx: ProvingContext,
        state: ProveGoalV2State,
        depth: int,
        max_depth: int,
    ) -> ProofResult:
        """Deterministic outcome selection from accumulated state."""

        logger.info(
            f"prove_goalv2: finalizing {ctx.goal_name} with "
            f"{len(state.proofs)} proof submission(s), {len(state.sketches)} sketch submission(s), "
            f"and {len(state.lemmas)} helper lemma submission(s)"
        )

        # Priority 1: Best typechecked proof
        best_proof = state.best_proof

        lemma_blocks = [*ctx.pending_lemma_blocks, *self._active_lemma_blocks(state)]

        if best_proof is not None:
            logger.info(f"prove_goalv2: found typechecked proof for {ctx.goal_name}")
            return await self._prover._finalize_result(
                ctx,
                ProofResult(
                    success=True,
                    content="",
                    proof=best_proof.proof,
                    lemmas=lemma_blocks,
                ),
            )

        # Priority 2: Best valid sketch → decompose + recurse
        best_sketch = state.best_sketch
        if best_sketch is not None and depth < max_depth:
            logger.info(
                f"prove_goalv2: decomposing {ctx.goal_name} into "
                f"{len(best_sketch.subgoals)} subgoals"
            )
            logger.info(
                f"prove_goalv2: carrying {len(lemma_blocks)} helper lemma block(s) into "
                f"decomposition of {ctx.goal_name}"
            )
            return await self._recurse_on_subgoals(
                ctx, best_sketch.subgoals, best_sketch.assembled_sketch,
                depth, max_depth, state.max_iterations, lemma_blocks,
            )

        # Priority 3: Failure
        n_proofs = len(state.proofs)
        n_sketches = len(state.sketches)
        logger.warning(
            f"prove_goalv2: exhausted for {ctx.goal_name} "
            f"({n_proofs} proofs, {n_sketches} sketches)"
        )
        failure_ctx = ctx.copy_with(pending_lemma_blocks=lemma_blocks)
        return await self._prover._fail_with_sorried_goal(
            failure_ctx,
            error=f"prove_goalv2 exhausted ({n_proofs} proofs, {n_sketches} sketches)",
            failures=[FailureInfo(
                phase="prove_goalv2",
                goal_name=ctx.goal_name,
                depth=depth,
                error=f"Exhausted {n_proofs} proof attempts, {n_sketches} sketch attempts",
            )],
        )

    # ── Subgoal recursion ────────────────────────────────────────

    async def _recurse_on_subgoals(
        self,
        ctx: ProvingContext,
        subgoals: list[SubgoalInfo],
        assembled_sketch: str,
        depth: int,
        max_depth: int,
        max_iterations: int,
        pending_lemma_blocks: list[str],
    ) -> ProofResult:
        """Recurse on extracted subgoals using the internal prove workflow."""
        from utils.lean.goals import exact_goal
        from utils.shutdown import handle_shutdown_if_requested, shutdown_hook, ShutdownHookMode

        all_failures: list[FailureInfo] = []
        subgoal_outcomes: list[SubgoalOutcome] = []
        running_lemma_blocks = list(pending_lemma_blocks)

        with shutdown_hook(
            ShutdownHookMode.PUSH,
            lambda: self.write_decomposition_shutdown_snapshot(
                ctx,
                subgoals=subgoals,
                assembled_sketch=assembled_sketch,
                extra_lemma_blocks=running_lemma_blocks,
            ),
        ):
            for sg_info in subgoals:
                handle_shutdown_if_requested(f"before proving subgoal {sg_info.name}")
                logger.info(f"prove_goalv2: proving subgoal {sg_info.name} at depth {depth + 1}")

                child_ctx = ctx.copy_with(
                    goal=sg_info.goal,
                    informal_reasoning="",
                    pending_lemma_blocks=running_lemma_blocks,
                )
                subgoal_result = await self._prove_goal(
                    ctx=child_ctx,
                    depth=depth + 1,
                    max_depth=max_depth,
                    max_iterations=max_iterations,
                )

                if subgoal_result.filtered_goal is not None:
                    old_invocation = exact_goal(sg_info.goal)
                    new_invocation = exact_goal(subgoal_result.filtered_goal)
                    if old_invocation != new_invocation:
                        logger.info(
                            f"  Updating invocation for {sg_info.name}: "
                            f"'{old_invocation}' -> '{new_invocation}'"
                        )
                        assembled_sketch = assembled_sketch.replace(old_invocation, new_invocation)

                outcome = SubgoalOutcome(
                    name=sg_info.name,
                    proof=subgoal_result.proof,
                    success=subgoal_result.success and not subgoal_result.has_sorry,
                    partial=subgoal_result.success and subgoal_result.has_sorry,
                    result=subgoal_result,
                )
                subgoal_outcomes.append(outcome)
                all_failures.extend(subgoal_result.failures)
                running_lemma_blocks = subgoal_result.lemmas

                if outcome.success:
                    logger.info(f"Proved subgoal {sg_info.name}")
                elif outcome.partial:
                    logger.info(f"Partially proved subgoal {sg_info.name} (with sorry)")
                else:
                    logger.warning(f"Failed to prove subgoal {sg_info.name}")

            subgoal_proofs = {o.name: o.proof for o in subgoal_outcomes}
            completely_failed = [o.name for o in subgoal_outcomes if not o.result.success]
            has_any_sorry = any(not o.success for o in subgoal_outcomes)

            await self._prover.load_sections_on_pantograph(ctx, ctx.sections[-1])
            assembly_result = await self._prover._finalize_proof(
                ctx,
                assembled_sketch=assembled_sketch,
                subgoal_proofs=subgoal_proofs,
                completely_failed_subgoals=completely_failed,
            )

            if not assembly_result["success"]:
                all_failures.append(FailureInfo(
                    phase="assembly",
                    goal_name=ctx.goal_name,
                    depth=depth,
                    error=assembly_result["error"],
                    attempted_proof=assembled_sketch,
                ))

            has_sorry_in_result = has_any_sorry or not assembly_result["success"]

            if has_sorry_in_result:
                sorry_count = sum(1 for o in subgoal_outcomes if not o.success)
                logger.info(
                    f"Goal proved with {sorry_count} subgoals using sorry at depth {depth}: {ctx.goal_name}"
                )
            else:
                logger.info(f"Successfully proved goal at depth {depth}: {ctx.goal_name}")

            return await self._prover._finalize_result(
                ctx.copy_with(pending_lemma_blocks=running_lemma_blocks),
                ProofResult(
                    success=True,
                    content="",
                    proof=assembly_result["proof"],
                    lemmas=running_lemma_blocks,
                    failures=all_failures,
                    has_sorry=has_sorry_in_result,
                ),
            )

    # ── Prompt construction (placeholder) ────────────────────────

    def _v2_build_system_prompt(self, ctx: ProvingContext) -> str:
        """Build system prompt for prove_goalv2."""
        return PROVE_GOAL_V2_SYSTEM

    def _v2_build_user_message(self, ctx: ProvingContext) -> str:
        """Build the per-goal user message with context."""
        file_context = ctx.get_relevant_context()

        parts = [
            f"## Theorem to Prove\n\n```lean\n{ctx.goal_theorem}\n```",
            f"## File Context\n\n```lean\n{file_context}\n```",
        ]

        if ctx.proof_hints:
            hints = ctx.proof_hints.format_hints()
            if hints:
                parts.append(f"## Known Hints\n\n{hints}")

        parts.append(self._tool_budget_summary(ctx))

        parts.append(f"Prove `{ctx.goal_name}`.")
        return "\n\n".join(parts)
