import re
from typing import Dict, Optional, Tuple, List, Literal, TYPE_CHECKING
from pathlib import Path
from dataclasses import dataclass, field

from dbos import DBOS
from langchain_core.messages import HumanMessage

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langgraph.graph import StateGraph
from providers import ReasoningLevel

from agents.base import BaseAgent
from config.timeouts import Timeouts
from utils.lean import unused_var_removal
from tools.automation import try_automation_tactics
from utils.lean.goals import exact_goal
from utils.lean.transform import (
    replace_first_sorry_with_multiline_tactic,
    replace_sorry_with_placeholder,
)
from utils.proof_types import (
    ProofResult, FailureInfo, ProvingContext, IterationFeedback,
    AutomationResult, SubgoalInfo, SubgoalOutcome, DecompositionResult,
    AttemptBudgetConfig, AttemptBudgetMode, ExistingPantographClient,
)
from agents.retriever_agent import (
    RetrieverAgent, RetrievalConfig, DiscoveryConfig,
)
from tools.proof_search import (
    LemmaDiscoveryConfig,
    ProofSearcher,
    TACTIC_WEIGHT_CORE,
    ValidatedTacticProofStatus,
    WeightedTactic,
    build_tactic_pool,
)
from agents.proof_reasoning_agent import ProofReasoningAgent
from prompts.prompts import SHALLOW_SOLVE_SYSTEM
from utils.lean.parser import LeanFile
from utils.lean.types import LakeBuildResult
from utils.lean.unused_var_removal import (
    filter_goal_params,
    remove_unused_vars,
    UnusedVarRemovalResult,
)
from utils.lean_helpers import extract_lean_code_from_md_block
from utils.lean_explore_service import DEFAULT_LEANEXPLORE_PACKAGES
from utils.message_constants import AGENT_PROMPT
from utils.message_helpers import (
    PromptSegment,
    bullets,
    create_prompt,
    render_prompt,
    section,
    stable,
    code_block,
    lean_block,
)
from utils.velvet_helpers import upsert_hints_block
from tools.pantograph_client import PantographClient, PantographFactory
from logging_config import get_logger
from utils.differ import Differ
from utils.shutdown import handle_shutdown_if_requested, shutdown_hook, ShutdownHookMode
from utils.escalation import AttemptContext, AttemptOutcome, run_with_escalation

logger = get_logger(__name__)

UNKNOWN_IDENTIFIER_RE = re.compile(r"Unknown identifier `([^`]+)`")


@DBOS.dbos_class()
class ProverAgent(BaseAgent):
    """Agent that generates and validates proofs for individual sub-problems.

    This agent focuses solely on proving - given a sub-problem and current
    file state, it generates a proof, validates it, and returns the result.

    Note: This agent doesn't use the graph-based workflow. Instead, it's
    invoked directly via prove_goal().
    """

    name = "prover"
    description = "Generates and validates Lean proofs for sub-problems"
    system_prompt: str = ""  # Not used - uses prompts from prompts.py directly

    def __init__(
        self,
        config: "LLMConfig",
        *,
        retriever: "RetrieverAgent",
        reasoning: "ProofReasoningAgent",
        section: str = "Proof",
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self._section = section
        self._retriever = retriever
        self._reasoning = reasoning
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    def build_graph(self) -> StateGraph:
        """Not used - this agent is invoked directly via prove_goal()."""
        raise NotImplementedError("ProverAgent doesn't use graph-based workflow")

    async def run_workflow(self, state: dict) -> dict:
        """Not used - this agent is invoked directly via prove_goal()."""
        raise NotImplementedError("ProverAgent doesn't use run_workflow. Use prove_goal() directly.")

    @staticmethod
    def _get_pantograph(ctx: ProvingContext) -> PantographClient:
        """Get the PantographClient for this proving context.

        Lazily creates the client if it doesn't exist (needed for DBOS resume).
        """
        params = ctx.pantograph
        existed = PantographFactory.has(params.key)
        client = PantographFactory.resolve_client(source=params)
        if not existed:
            logger.info(f"[_get_pantograph] Created PantographClient for key '{params.key}'")
        return client

    @staticmethod
    async def load_sections_on_pantograph(ctx: ProvingContext, sections: str | list[str]) :
        if isinstance(sections, str):
            sections = [sections]
        lean_file = LeanFile.from_path(ctx.file_path)
        content = "\n\n".join([ lean_file.get_section(section,assert_exists=True).full_text() for section in sections  ])
        return await (ProverAgent._get_pantograph(ctx)).load_definitions(ctx.pantograph.key, content)

    @DBOS.step()
    async def _discover_hints(self, ctx: ProvingContext):
        """Read hint sections from file and discover proof hints via Pantograph.

        Also upserts a marked hints block in the Proof section so all subsequent
        proving steps (including recursion) can benefit from grind/solver hints.
        """
        self._get_pantograph(ctx)
        lean_file = LeanFile.from_path(ctx.file_path)
        code = "\n\n".join(
            lean_file.get_section(s, assert_exists=True).full_text()
            for s in ctx.hint_sections
        )
        proof_hints = await self._retriever.discover_proof_hints(
            source=ExistingPantographClient(key=ctx.pantograph.key),
            code=code,
            config=DiscoveryConfig(
                dep_graph_depth=1,
                lemma_discovery=LemmaDiscoveryConfig(),
            ),
        )

        # Idempotently maintain `-- HINTS BEGIN/END` block in Proof section.
        proof_section = lean_file.get_section(self._section)
        if proof_section is not None:
            updated = upsert_hints_block(
                proof_section.content,
                proof_hints.grindable_lemmas,
            )
            if updated != proof_section.content:
                lean_file.add_or_replace_section(self._section, updated)
                lean_file.reconstruct_and_write_to_file(Path(ctx.file_path))
                logger.info(
                    f"Updated {self._section} hints block with "
                    f"{len(proof_hints.grindable_lemmas)} grindable lemma(s)"
                )

        return proof_hints

    @DBOS.workflow()
    async def prove(
        self,
        ctx: ProvingContext,
        max_depth: int = 4,
    ) -> ProofResult:
        """Entry point for proving a goal.

        Discovers proof hints from hint_sections if needed (skipped when
        ctx.proof_hints is already set). Then delegates to prove_goal().
        """
        if ctx.hint_sections and not ctx.proof_hints:
            proof_hints = await self._discover_hints(ctx)
            logger.info("Discovered proof hints:\n%s", proof_hints)
            ctx = ctx.copy_with()
            ctx.proof_hints = proof_hints

        return await self.prove_goal(ctx, depth=1, max_depth=max_depth)

    @DBOS.workflow()
    async def prove_goal(
        self,
        ctx: ProvingContext,
        depth: int = 1,
        max_depth: int = 4,
    ) -> ProofResult:
        """Prove a goal using HILBERT-style recursive decomposition."""
        with shutdown_hook(ShutdownHookMode.PUSH, lambda: self.write_shutdown_snapshot(ctx)):
            # Load sections specified by caller on pantograph
            await self.load_sections_on_pantograph(ctx, ctx.sections)

            logger.info(f"{'=' * 80}")
            logger.info(f"Proving goal at depth {depth}/{max_depth}: {ctx.goal_name}")
            logger.info(f"{'=' * 80}")

            if depth > max_depth:
                logger.warning(f"Maximum recursion depth {max_depth} reached")
                return await self._fail_with_sorried_goal(
                    ctx,
                    error=f"Maximum recursion depth {max_depth} reached",
                    failures=[FailureInfo(
                        phase="max_depth",
                        goal_name=ctx.goal_name,
                        depth=depth,
                        error="Maximum recursion depth reached",
                    )],
                )

            automation_result = await self._try_automation(ctx)
            if automation_result.success:
                assert automation_result.build_result is not None
                return await self._finalize_result(
                    ctx,
                    ProofResult(success=True, content="", proof=automation_result.proof),
                )

            handle_shutdown_if_requested(f"before informal reasoning for {ctx.goal_name}")
            reasoning_result = await self._reasoning.generate_informal_reasoning(
                goal_theorem=ctx.goal_theorem,
                relevant_context=ctx.get_relevant_context(),
            )
            ctx.informal_reasoning = reasoning_result.informal_reasoning

            handle_shutdown_if_requested(f"before shallow solve for {ctx.goal_name}")
            shallow_iterations = self._resolve_attempt_budget(
                ctx.attempt_budgets.shallow,
                depth=depth,
                max_depth=max_depth,
            )
            logger.info(
                f"[Depth {depth}] Step 1: Attempting shallow solve ({shallow_iterations} iterations)..."
            )
            shallow_result = await self._try_shallow_solve(
                ctx,
                cur_depth=depth,
                max_iterations=shallow_iterations,
            )

            if shallow_result.success:
                logger.info(f"✓ Shallow solve succeeded at depth {depth}")
                return await self._finalize_result(
                    ctx,
                    ProofResult(success=True, content="", proof=shallow_result.proof),
                )

            logger.info(
                f"✗ Shallow solve failed at depth {depth}, proceeding to decomposition"
            )
            all_failures = shallow_result.failures.copy()

            handle_shutdown_if_requested(f"before decomposition for {ctx.goal_name}")
            if depth == max_depth:
                logger.info(
                    f"At max depth {max_depth}, skipping decomposition (subgoals would exceed depth limit)"
                )
                all_failures.append(FailureInfo(
                    phase="shallow_solve_at_max_depth",
                    goal_name=ctx.goal_name,
                    depth=depth,
                    error="Shallow solve failed at max depth, decomposition skipped",
                ))
                return await self._fail_with_sorried_goal(
                    ctx,
                    error="Shallow solve failed at max depth",
                    failures=all_failures,
                )

            decomposition_attempts = self._resolve_attempt_budget(
                ctx.attempt_budgets.decomposition,
                depth=depth,
                max_depth=max_depth,
            )
            logger.info(
                f"[Depth {depth}] Step 2: Decomposing goal into subgoals ({decomposition_attempts} attempts)..."
            )
            decomposition_result = await self._decompose_into_subgoals(
                ctx,
                max_attempts=decomposition_attempts,
            )

            if not decomposition_result["success"]:
                logger.warning(
                    f"✗ Decomposition failed at depth {depth}, returning goal with sorry"
                )
                all_failures.append(FailureInfo(
                    phase="decomposition",
                    goal_name=ctx.goal_name,
                    depth=depth,
                    error=decomposition_result["error"],
                ))
                return await self._fail_with_sorried_goal(
                    ctx,
                    error=decomposition_result["error"],
                    failures=all_failures,
                )

            assembled_sketch = decomposition_result["assembled_sketch"]
            subgoal_infos: list[SubgoalInfo] = decomposition_result["subgoals"]
            logger.info(f"✓ Successfully decomposed into {len(subgoal_infos)} subgoals")
            logger.info(f"[Depth {depth}] Step 3: Proving {len(subgoal_infos)} subgoals...")
            subgoal_outcomes: List[SubgoalOutcome] = []

            with shutdown_hook(
                ShutdownHookMode.PUSH,
                lambda: self.write_decomposition_shutdown_snapshot(
                    ctx,
                    subgoals=subgoal_infos,
                    assembled_sketch=assembled_sketch,
                ),
            ):
                for sg_info in subgoal_infos:
                    handle_shutdown_if_requested(f"before proving subgoal {sg_info.name}")
                    logger.info(f"Proving subgoal {sg_info.name}")

                    child_ctx = ctx.copy_with(
                        goal=sg_info.goal,
                        informal_reasoning="",
                    )
                    subgoal_result = await self.prove_goal(
                        ctx=child_ctx,
                        depth=depth + 1,
                        max_depth=max_depth,
                    )

                    if subgoal_result.filtered_goal is not None:
                        old_invocation = exact_goal(sg_info.goal)
                        new_invocation = exact_goal(subgoal_result.filtered_goal)
                        if old_invocation != new_invocation:
                            logger.info(
                                f"  Updating invocation for {sg_info.name}: "
                                f"'{old_invocation}' -> '{new_invocation}'"
                            )
                            assembled_sketch = assembled_sketch.replace(
                                old_invocation, new_invocation
                            )

                    outcome = SubgoalOutcome(
                        name=sg_info.name,
                        proof=subgoal_result.proof,
                        success=subgoal_result.success and not subgoal_result.has_sorry,
                        partial=subgoal_result.success and subgoal_result.has_sorry,
                        result=subgoal_result,
                    )
                    subgoal_outcomes.append(outcome)
                    all_failures.extend(subgoal_result.failures)

                    if outcome.success:
                        logger.info(f"✓ Proved subgoal {sg_info.name}")
                    elif outcome.partial:
                        logger.info(f"⚠ Partially proved subgoal {sg_info.name} (with sorry)")
                    else:
                        logger.warning(f"✗ Failed to prove subgoal {sg_info.name}, will use sorry")

                logger.info(f"[Depth {depth}] Step 4: Assembling final proof from subgoals...")
                subgoal_proofs = {o.name: o.proof for o in subgoal_outcomes}
                completely_failed = [o.name for o in subgoal_outcomes if not o.result.success]
                has_any_sorry = any(not o.success for o in subgoal_outcomes)

                await self.load_sections_on_pantograph(ctx, self._section)
                assembly_result = await self._finalize_proof(
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

                has_failures = has_any_sorry or not assembly_result["success"]
                has_sorry_in_result = has_failures
                if has_failures:
                    sorry_count = sum(1 for o in subgoal_outcomes if not o.success)
                    logger.info(
                        f"⚠ Goal proved with {sorry_count} subgoals using sorry at depth {depth}: {ctx.goal_name}"
                    )
                else:
                    logger.info(f"✓ Successfully proved goal at depth {depth}: {ctx.goal_name}")

                return await self._finalize_result(
                    ctx,
                    ProofResult(
                        success=True,
                        content="",
                        proof=assembly_result["proof"],
                        failures=all_failures,
                        has_sorry=has_sorry_in_result,
                    ),
                )


    async def _fail_with_sorried_goal(
        self,
        ctx: ProvingContext,
        error: str,
        failures: list[FailureInfo],
    ) -> ProofResult:
        """Write a sorried goal to the temp section and return a finalized failure.

        This is the standard bail-out path: write the sorried theorem so the
        parent can merge it, then finalize.
        """
        result = ProofResult(
            success=False,
            content=Path(ctx.file_path).read_text(),
            proof=ctx.goal_theorem,
            lemmas=ctx.pending_lemma_blocks,
            error=error,
            failures=failures,
            has_sorry=True,
        )
        return await self._finalize_result(ctx, result)

    @staticmethod
    def _missing_blocks(existing_content: str, blocks: list[str]) -> list[str]:
        """Return non-empty proof blocks that are not already present."""
        missing: list[str] = []
        seen: set[str] = set()
        for block in blocks:
            normalized = block.strip()
            if not normalized or normalized in seen or normalized in existing_content:
                continue
            seen.add(normalized)
            missing.append(normalized)
        return missing

    @staticmethod
    def _proof_has_goal_declaration(proof_content: str, goal_name: str) -> bool:
        """Return whether Proof already declares the given theorem/lemma name."""
        def is_goal_decl(line: str, keyword: str) -> bool:
            stripped = line.lstrip()
            prefix = f"{keyword} {goal_name}"
            if not stripped.startswith(prefix):
                return False
            if len(stripped) == len(prefix):
                return True
            return stripped[len(prefix)].isspace() or stripped[len(prefix)] in "(:"

        return any(
            is_goal_decl(line, "theorem") or is_goal_decl(line, "lemma")
            for line in proof_content.splitlines()
        )

    def write_shutdown_snapshot(
        self,
        ctx: ProvingContext,
        *,
        extra_lemma_blocks: Optional[list[str]] = None,
    ) -> str:
        """Best-effort shutdown snapshot that preserves on-disk proof progress.

        Reads the current file from disk so completed subgoals/helper lemmas
        remain intact, appends any still-pending helper lemmas to the main
        proof section, and records the current goal there as a sorried theorem
        if it has not already been finalized.
        """
        file_path = Path(ctx.file_path)
        current_program = file_path.read_text() if file_path.exists() else ""
        lean_file = LeanFile.from_content(current_program)

        if not lean_file.has_section(self._section):
            lean_file.add_or_replace_section(self._section, "")

        proof_section = lean_file.get_section(self._section, assert_exists=True)
        existing_section_content = proof_section.full_text()
        pending_blocks = [
            *ctx.pending_lemma_blocks,
            *(extra_lemma_blocks or []),
        ]
        missing_blocks = self._missing_blocks(existing_section_content, pending_blocks)
        if missing_blocks:
            lean_file.append_in_section(
                self._section,
                "\n\n".join(missing_blocks),
                assert_section_present=True,
            )
            proof_section = lean_file.get_section(self._section, assert_exists=True)

        if not self._proof_has_goal_declaration(proof_section.content, ctx.goal_name):
            lean_file.append_in_section(
                self._section,
                ctx.goal_theorem,
                assert_section_present=True,
            )

        lean_file.remove_section(ctx.temp_section)

        final_content = lean_file.reconstruct_and_write_to_file(file_path)
        logger.info(
            "Shutdown snapshot preserved progress for %s at %s",
            ctx.goal_name,
            ctx.file_path,
        )
        return final_content

    def write_decomposition_shutdown_snapshot(
        self,
        ctx: ProvingContext,
        *,
        subgoals: list[SubgoalInfo],
        assembled_sketch: str,
        extra_lemma_blocks: Optional[list[str]] = None,
    ) -> str:
        """Preserve a decomposed parent goal and unfinished children on shutdown."""
        file_path = Path(ctx.file_path)
        current_program = file_path.read_text() if file_path.exists() else ""
        lean_file = LeanFile.from_content(current_program)

        if not lean_file.has_section(self._section):
            lean_file.add_or_replace_section(self._section, "")

        proof_section = lean_file.get_section(self._section, assert_exists=True)
        existing_section_content = proof_section.full_text()
        pending_blocks = [
            *ctx.pending_lemma_blocks,
            *(extra_lemma_blocks or []),
        ]
        missing_blocks = self._missing_blocks(existing_section_content, pending_blocks)
        if missing_blocks:
            lean_file.append_in_section(
                self._section,
                "\n\n".join(missing_blocks),
                assert_section_present=True,
            )
            proof_section = lean_file.get_section(self._section, assert_exists=True)

        for subgoal in subgoals:
            if self._proof_has_goal_declaration(proof_section.content, subgoal.name):
                continue
            lean_file.append_in_section(
                self._section,
                subgoal.statement,
                assert_section_present=True,
            )
            proof_section = lean_file.get_section(self._section, assert_exists=True)

        if (
            assembled_sketch.strip()
            and not self._proof_has_goal_declaration(proof_section.content, ctx.goal_name)
        ):
            lean_file.append_in_section(
                self._section,
                assembled_sketch,
                assert_section_present=True,
            )

        lean_file.remove_section(ctx.temp_section)

        final_content = lean_file.reconstruct_and_write_to_file(file_path)
        logger.info(
            "Shutdown decomposition snapshot preserved %s with %d subgoal(s) at %s",
            ctx.goal_name,
            len(subgoals),
            ctx.file_path,
        )
        return final_content

    @DBOS.step()
    async def _finalize_result(
        self,
        ctx: ProvingContext,
        result: ProofResult,
    ) -> ProofResult:
        """Finalize a proof result - remove unused vars and move to main section.

        This is the SINGLE place where we decide how to finalize based on the result.
        All proving logic should just build results, and call this at the end.

        Args:
            ctx: Proving context with file_path, goal, temp_section
            result: The proof result (with content still in temp section)

        Returns:
            Updated ProofResult with final content
        """
        build_results = await self._get_pantograph(ctx).check_build(result.proof)
        build_results.assert_typechecks("_finalize_result: proof must typecheck before finalization")
        # Skip unused var removal for loom_auto proofs — it's an SMT tactic that
        # uses hypotheses implicitly, so the linter falsely flags them as unused.
        if "loom_auto" in result.proof:
            logger.info(f"Skipping unused var removal for {ctx.goal_name}: proof uses loom_auto")
            unused_var_removal_result = UnusedVarRemovalResult(goal=ctx.goal, theorem=result.proof, changed=False)
        else:
            prev_result = UnusedVarRemovalResult(goal=ctx.goal, theorem=result.proof, changed=False)
            unused_var_removal_result = remove_unused_vars(ctx.goal, result.proof, build_results.diagnostics)
            while unused_var_removal_result.changed:
                build_results = await self._get_pantograph(ctx).check_build(unused_var_removal_result.theorem)
                if not build_results.typechecks:
                    logger.warning(
                        f"Unused var removal broke typecheck for {ctx.goal_name}, reverting"
                    )
                    unused_var_removal_result = prev_result
                    break
                prev_result = unused_var_removal_result
                unused_var_removal_result = remove_unused_vars(unused_var_removal_result.goal, unused_var_removal_result.theorem, build_results.diagnostics)

        # Move to main section
        lean_file = LeanFile.from_content(Path(ctx.file_path).read_text())

        # Add this goal's proof to main section and remove temp section
        if result.lemmas:
            proof_section = lean_file.get_section(self._section, assert_exists=True)
            existing_section_content = proof_section.full_text()
            lemma_blocks = self._missing_blocks(existing_section_content, result.lemmas)
            if lemma_blocks:
                lean_file.append_in_section(
                    self._section,
                    "\n\n".join(lemma_blocks),
                    assert_section_present=True,
                )

        lean_file.append_in_section(self._section, unused_var_removal_result.theorem, assert_section_present=True)
        lean_file.remove_section(ctx.temp_section)
        final_content = lean_file.reconstruct_and_write_to_file(Path(ctx.file_path))

        return ProofResult(
            success=result.success,
            content=final_content,
            proof=unused_var_removal_result.theorem,
            error=result.error,
            failures=result.failures,
            has_sorry=result.has_sorry,
            filtered_goal=unused_var_removal_result.goal,
            lemmas=[],
        )

    @staticmethod
    def _proof_search_tactic_pool(ctx: ProvingContext) -> list[WeightedTactic]:
        """Build proof-search tactic pool from discovered hints + automation tactics."""
        if ctx.proof_hints:
            pool = build_tactic_pool(
                [l.name for l in ctx.proof_hints.discovered_lemmas],
                ctx.proof_hints.user_constants,
                ctx.proof_hints.user_constructors,
            )
        else:
            pool = build_tactic_pool([], [], [])

        seen = {wt.tactic for wt in pool}
        for tactic in ctx.automation_tactics:
            if tactic not in seen:
                seen.add(tactic)
                pool.append(WeightedTactic(tactic, TACTIC_WEIGHT_CORE))
        return pool

    @staticmethod
    def _tactic_script_from_recovered(result) -> list[str]:
        return [t.rstrip() for t in (result.recover_tactics() or []) if t.strip()]

    async def _try_automation_with_proof_search(
        self,
        ctx: ProvingContext,
    ) -> AutomationResult:
        """Try fast automation first, but skip the proof-search execution path."""
        pantograph = self._get_pantograph(ctx)
        automation_res = await try_automation_tactics(
            pantograph,
            ctx.goal_theorem,
            ctx.automation_tactics,
        )
        if automation_res.success:
            if automation_res.proof:
                logger.info(
                    "Automation tactics solved %s with theorem:\n%s",
                    ctx.goal_name,
                    automation_res.proof.rstrip(),
                )
            return automation_res

        logger.info("Automation tactics failed for %s; trying proof search", ctx.goal_name)
        searcher = ProofSearcher(
            pantograph,
            tactic_pool=self._proof_search_tactic_pool(ctx),
        )
        logger.info(
            "Skipping search_validated_tactic_proof for %s; proof search execution disabled",
            ctx.goal_name,
        )
        _ = searcher
        _ = Timeouts.PROOF_SEARCH
        _ = ValidatedTacticProofStatus
        return automation_res

    @DBOS.step()
    async def _try_automation(
        self,
        ctx: ProvingContext,
    ) -> AutomationResult:
        logger.info("Trying automation for theorem")
        return await self._try_automation_with_proof_search(ctx)


    # NOTE: No @DBOS.step() - this orchestrates the loop, individual attempts are steps
    async def _try_shallow_solve(
        self,
        ctx: ProvingContext,
        cur_depth: int,
        max_iterations: int = 5,
    ) -> ProofResult:

        # Combine proof hints (from discovery) with semantic search hints
        semantic_hints = await self._retriever.retrieve_hints(
            goal_theorem=ctx.goal_theorem,
            relevant_context=ctx.get_relevant_context(),
            informal_reasoning=ctx.informal_reasoning,
            config=RetrievalConfig(
                num_semantic_queries=7,
                semantic_results_per_query=2,
                semantic_package_filters=list(DEFAULT_LEANEXPLORE_PACKAGES),
            ),
            validate_with=ctx.pantograph,
        )
        hint_parts = []
        if ctx.proof_hints:
            hint_parts.append(ctx.proof_hints.format_hints())
        if semantic_hints:
            hint_parts.append(semantic_hints)
        hints = "\n\n".join(hint_parts)

        if hints:
            logger.info(f"Retrieved hints for shallow solve")

        logger.info(
            f"Attempting shallow solve for {ctx.goal_name} ({max_iterations} iterations)"
        )

        all_failures: List[FailureInfo] = []

        # Build static system context once (for caching)
        static_context = self._build_shallow_solve_system_context(
            ctx,
            hints=hints,
        )
        system_content = f"{SHALLOW_SOLVE_SYSTEM}\n\n{static_context}"

        async def attempt(
            attempt_ctx: AttemptContext,
            prev_failure: IterationFeedback,
            reasoning_level: ReasoningLevel | None,
        ) -> AttemptOutcome[ProofResult, IterationFeedback]:
            handle_shutdown_if_requested(
                f"shallow solve iteration {attempt_ctx.attempt_index}"
            )
            logger.info(
                "  Shallow solve iteration %d/%d",
                attempt_ctx.attempt_index + 1,
                attempt_ctx.max_attempts,
            )
            result = await self._shallow_solve_attempt(
                ctx,
                attempt_ctx.attempt_index,
                system_content,
                cur_depth,
                prev_failure,
                reasoning_level,
            )

            if not result.success:
                prev_failure.error = result.error
                if result.failures:
                    all_failures.extend(result.failures)
                return AttemptOutcome(
                    success=False,
                    value=result,
                    failure=prev_failure,
                )

            return AttemptOutcome(success=True, value=result, failure=None)

        outcome = await run_with_escalation(
            max_attempts=max_iterations,
            escalation=self._select_shallow_reasoning_level,
            attempt=attempt,
            feedback_factory=IterationFeedback,
        )

        if outcome.success:
            logger.info("  ✓ Shallow solve succeeded")
            assert outcome.value is not None
            return outcome.value

        logger.info(f"  ✗ Shallow solve failed after {max_iterations} iterations")
        return ProofResult(
            success=False,
            content=ctx.read_file(),
            proof="",
            error=f"Shallow solve failed after {max_iterations} iterations",
            failures=all_failures,
        )

    @staticmethod
    def _resolve_attempt_budget(
        config: AttemptBudgetConfig,
        *,
        depth: int,
        max_depth: int,
    ) -> int:
        """Resolve attempt budget based on depth and configuration."""
        depth_offset = max(depth - 1, 0)
        if config.mode == AttemptBudgetMode.UP:
            value = config.base + config.slope * depth_offset
        elif config.mode == AttemptBudgetMode.DOWN:
            value = config.base - config.slope * depth_offset
        else:
            raise ValueError(f"Unsupported attempt budget mode: {config.mode}")

        return max(config.min_attempts, min(config.max_attempts, value))

    @staticmethod
    def _select_shallow_reasoning_level(
        attempt_ctx: AttemptContext,
    ) -> ReasoningLevel | None:
        """Select reasoning level for shallow solve attempts.

        Escalates to LOW reasoning when half the attempts are exhausted.
        """
        remaining = attempt_ctx.max_attempts - attempt_ctx.attempt_index
        if remaining <= max(1, attempt_ctx.max_attempts // 2):
            return ReasoningLevel.LOW
        return None

    @staticmethod
    def _select_decomposition_reasoning_level(
        attempt_ctx: AttemptContext,
    ) -> ReasoningLevel | None:
        """Select reasoning level for decomposition attempts.

        Currently always returns None to keep costs down.
        Add logic here to bump/downgrade reasoning based on attempt_ctx if needed.

        For example, you could escalate when a third of attempts are exhausted:
            remaining = attempt_ctx.max_attempts - attempt_ctx.attempt_index
            if remaining <= max(1, attempt_ctx.max_attempts // 3):
                return ReasoningLevel.HIGH
        """
        return None

    @DBOS.step()
    async def _shallow_solve_attempt(
        self,
        ctx: ProvingContext,
        iteration: int,
        system_content: str,
        cur_depth: int,
        feedback: IterationFeedback,
        reasoning_level: ReasoningLevel | None,
    ) -> ProofResult:
        """Single shallow solve attempt - LLM call + validation + typecheck.

        This is a DBOS step so each iteration is checkpointed independently.
        """
        # Build messages: static system context + dynamic user message
        messages = []
        messages.append(
            self.create_system_message(
                content=system_content, message_type=AGENT_PROMPT
            )
        )

        user_message = self._build_shallow_solve_user_message(
            ctx, feedback, iteration,
        )
        messages.append(HumanMessage(content=user_message))

        # Get LLM response (complete theorem)
        logger.info(f"    Requesting proof from LLM...")
        response = await self.ainvoke_llm(messages, reasoning_level=reasoning_level)
        llm_output = response.content
        complete_theorem = extract_lean_code_from_md_block(llm_output).strip()

        logger.info(
            f"    THEOREM:\n{'-' * 80}\n{complete_theorem}\n{'-' * 80}"
        )

        # VERIFY: Check that the signature matches
        sig_error = self._validate_theorem_signature(complete_theorem, ctx)
        if sig_error:
            logger.info(f"    ✗ Signature mismatch, rejecting LLM output")
            return ProofResult(
                success=False,
                content=ctx.read_file(),
                proof="",
                error=sig_error,
            )

        # Check if the proof contains sorry
        if "sorry" in complete_theorem:
            logger.warning(f"    ✗ Proof contains 'sorry', rejecting")
            return ProofResult(
                success=False,
                content=ctx.read_file(),
                proof="",
                error=f"""YOUR PROOF CONTAINS 'sorry' WHICH IS NOT ALLOWED:

Your theorem:
```lean
{complete_theorem}
```

**ERROR**: The proof uses `sorry` which is a placeholder for unfinished proofs.
You MUST provide a complete proof without any `sorry`.

Please provide a fully complete proof with no `sorry`.""",
            )

        # Typecheck
        typecheck_result = await self._get_pantograph(ctx).check_build(complete_theorem)

        if typecheck_result.typechecks:
            #  Not writing anything to a file
            return ProofResult(
                success=True,
                content=ctx.read_file(),
                proof=complete_theorem,
            )

        error_msg = self._typecheck_error_feedback(complete_theorem, typecheck_result)
        return ProofResult(
            success=False,
            content=ctx.read_file(),
            proof="",
            error=error_msg,
            failures=[
                FailureInfo(
                    phase="shallow_solve",
                    goal_name=ctx.goal_name,
                    depth=cur_depth,
                    error=error_msg,
                    attempted_proof=complete_theorem,
                )
            ],
        )

    # NOTE: No @DBOS.step() - this orchestrates the loop, individual attempts are steps
    async def _decompose_into_subgoals(
        self,
        ctx: ProvingContext,
        max_attempts: int = 5,
    ) -> dict:

        logger.info(
            f"Decomposing goal {ctx.goal_name} into subgoals (max {max_attempts} attempts)"
        )

        # Combine proof hints (from discovery) with semantic search hints
        semantic_hints = await self._retriever.retrieve_hints(
            goal_theorem=ctx.goal_theorem,
            relevant_context=ctx.get_relevant_context(),
            informal_reasoning=ctx.informal_reasoning,
            config=RetrievalConfig(
                num_semantic_queries=7,
                semantic_results_per_query=2,
                semantic_package_filters=list(DEFAULT_LEANEXPLORE_PACKAGES),
            ),
            validate_with=ctx.pantograph,
        )
        hint_parts = []
        if ctx.proof_hints:
            hint_parts.append(ctx.proof_hints.format_hints())
        if semantic_hints:
            hint_parts.append(semantic_hints)
        hints = "\n\n".join(hint_parts)
        if hints:
            logger.info("Retrieved hints for decomposition")

        # Filter file content for the prompt (static across attempts - API caches)
        file_context = ctx.get_relevant_context()

        async def attempt(
            attempt_ctx: AttemptContext,
            prev_failure: IterationFeedback,
            reasoning_level: ReasoningLevel | None,
        ) -> AttemptOutcome[dict, IterationFeedback]:
            handle_shutdown_if_requested(
                f"decomposition attempt {attempt_ctx.attempt_index}"
            )
            logger.info(
                "  Decomposition attempt %d/%d",
                attempt_ctx.attempt_index + 1,
                attempt_ctx.max_attempts,
            )
            result = await self._decomposition_attempt(
                ctx,
                attempt_ctx.attempt_index,
                file_context,
                hints,
                prev_failure,
                reasoning_level,
            )

            if not result.get("success", False):
                prev_failure.error = result.get("error_feedback")
                prev_failure.previous_attempt = result.get("previous_attempt")
                return AttemptOutcome(
                    success=False,
                    value=result,
                    failure=prev_failure,
                )

            return AttemptOutcome(success=True, value=result, failure=None)

        outcome = await run_with_escalation(
            max_attempts=max_attempts,
            escalation=self._select_decomposition_reasoning_level,
            attempt=attempt,
            feedback_factory=IterationFeedback,
        )

        if outcome.success:
            logger.info("  ✓ Decomposition succeeded")
            assert outcome.value is not None
            return outcome.value

        logger.warning(f"  ✗ Decomposition failed after {max_attempts} attempts")
        return {
            "success": False,
            "sketch": "",
            "subgoals": [],
            "error": f"Decomposition failed after {max_attempts} attempts",
        }

    async def _decomposition_attempt(
        self,
        ctx: ProvingContext,
        attempt: int,
        file_context: str,
        hints: Optional[str],
        feedback: IterationFeedback,
        reasoning_level: ReasoningLevel | None,
    ) -> dict:
        """Single decomposition attempt - orchestrates inner steps.

        Not a @DBOS.step() so that inner steps (generate_proof_sketch,
        check_goals_correctness_batch) are independently checkpointed from
        the parent prove_goal workflow. File I/O between them is deterministic
        (same file state from cached steps) and always reverts the file.
        """
        # Use ProofReasoningAgent to generate proof sketch
        sketch_result = await self._reasoning.generate_proof_sketch(
            goal_theorem=ctx.goal_theorem,
            file_context=file_context,
            informal_reasoning=ctx.informal_reasoning,
            hints=hints,
            error_feedback=feedback.error,
            reasoning_level=reasoning_level,
        )

        if not sketch_result.success:
            logger.warning(f"    ✗ Sketch generation failed: {sketch_result.error}")
            return {
                "success": False,
                "error_feedback": f"Previous attempt failed: {sketch_result.error}",
                "previous_attempt": feedback.previous_attempt,
            }

        complete_theorem = sketch_result.sketch
        logger.info(f"    Generated proof sketch ({len(complete_theorem)} chars)")

        # Log diff with previous attempt
        if feedback.previous_attempt is not None:
            differ = Differ("previous_sketch", feedback.previous_attempt, "current_sketch", complete_theorem)
            diff_str = differ.format()
            if diff_str:
                logger.info(f"    DIFF FROM PREVIOUS SKETCH:\n{'-' * 80}\n{diff_str}\n{'-' * 80}")
            else:
                logger.info("    DIFF: No changes from previous sketch (identical)")

        # VERIFY: Check that the signature matches
        sig_error = self._validate_theorem_signature(complete_theorem, ctx)
        if sig_error:
            return {
                "success": False,
                "error_feedback": f"PREVIOUS ATTEMPT FAILED:\n{sig_error}",
                "previous_attempt": complete_theorem,
            }

        proof_with_sorries = complete_theorem

        # Validate that the skeleton typechecks
        typecheck_result = await self._typecheck_sketch(ctx, proof_with_sorries)

        if not typecheck_result.typechecks:
            error_msg = self._typecheck_error_feedback(proof_with_sorries, typecheck_result)
            logger.warning(f"    ✗ Proof sketch failed to typecheck")
            return {
                "success": False,
                "error_feedback": error_msg,
                "previous_attempt": complete_theorem,
            }

        logger.info(f"    ✓ Proof sketch with sorries typechecks")

        # Extract subgoals from the sketch and build assembled proof template
        decomp = await self._extract_subgoals_from_sketch(
            ctx, proof_with_sorries
        )

        if not decomp.success:
            logger.warning(f"    ✗ Subgoal extraction failed: {decomp.error}")
            return {
                "success": False,
                "error_feedback": f"SUBGOAL EXTRACTION FAILED:\n{decomp.error}",
                "previous_attempt": complete_theorem,
            }

        subgoal_infos = decomp.subgoals
        assembled_sketch = decomp.assembled_sketch

        logger.info(f"    EXTRACTED SUBGOALS:")
        # === Correctness Check Integration (batched) ===
        invalid_subgoals = []

        if subgoal_infos:
            from agents.proof_reasoning_agent import GoalCheckInput

            # Build batch inputs for all subgoals
            goal_inputs = [
                GoalCheckInput(
                    goal_id=sg_info.name,
                    goal_statement=sg_info.statement,
                )
                for sg_info in subgoal_infos
            ]

            logger.info(f"      Checking correctness of {len(goal_inputs)} subgoals in one batch")
            shared_ctx = {"File Context": file_context}
            if hints:
                shared_ctx["Available Lemmas and Hints"] = hints
            check_results = await self._reasoning.check_goals_correctness_batch(
                goals=goal_inputs,
                shared_context=shared_ctx,
                reasoning_level=reasoning_level,
            )

            # Collect all invalid subgoals
            for sg_info, check_result in zip(subgoal_infos, check_results):
                if not check_result.is_provable:
                    invalid_subgoals.append({
                        "name": sg_info.name,
                        "statement": sg_info.statement,
                        "justification": check_result.justification or "No justification provided",
                        "hint": check_result.correction_hint or "",
                    })
                    logger.warning(f"      ✗ Subgoal {sg_info.name} marked as invalid/unprovable")
                else:
                    logger.info(f"      ✓ Subgoal {sg_info.name} marked as correct")

        if invalid_subgoals:
            # Log the entire payload for debugging
            import json
            logger.warning(f"Invalid subgoals payload:\n{json.dumps(invalid_subgoals, indent=2)}")

            # Format all invalid subgoals
            invalid_parts = []
            for inv in invalid_subgoals:
                invalid_parts.append(f"""Subgoal `{inv["name"]}`:
```lean
{inv["statement"]}
```
**Reason:** {inv["justification"]}
**Hint:** {inv["hint"]}""")

            return {
                "success": False,
                "error_feedback": f"""YOUR SUBGOAL DECOMPOSITION CONTAINS {len(invalid_subgoals)} MATHEMATICALLY INCORRECT/UNPROVABLE SUBGOAL(S):

{chr(10).join(invalid_parts)}

Please regenerate the proof sketch using mathematically valid subgoals.""",
                "previous_attempt": complete_theorem,
            }

        logger.info(
            f"    ✓ All {len(subgoal_infos)} subgoals verified as mathematically correct"
        )

        return {
            "success": True,
            "sketch": proof_with_sorries,
            "assembled_sketch": assembled_sketch,
            "subgoals": subgoal_infos,
            "error": "",
        }

    @DBOS.step()
    async def _typecheck_sketch(
        self,
        ctx: ProvingContext,
        content: str,
    ) -> LakeBuildResult:
        """Write content to section, typecheck, and always revert.

        Used to validate a proof sketch without persisting it.
        """
        return await self._get_pantograph(ctx).check_build(content)

    @DBOS.step()
    async def _extract_subgoals_from_sketch(
        self,
        ctx: ProvingContext,
        proof_sketch: str
    ) -> DecompositionResult:
        parent_info = ctx.goal
        parent_name = parent_info.name

        # Replace sorry with expose_names; sorry to avoid ghost variables in extracted goals
        proof_sketch_with_expose = replace_sorry_with_placeholder(proof_sketch, "expose_names; sorry")
        logger.info("Proof sketch with expose_names:\n%s", proof_sketch_with_expose)
        goals, _ = await self._get_pantograph(ctx).extract_subgoals(proof_sketch_with_expose, parent_name)

        # Sanity check: each extracted subgoal's sorry theorem must typecheck.
        # Decomposition can produce goals with malformed types (e.g. Nat.rec in the
        # target) that Lean can't elaborate standalone. Reject the whole sketch early.
        pantograph = self._get_pantograph(ctx)
        for goal in goals:
            build = await pantograph.check_build(goal.as_sorried())
            if not build.typechecks:
                logger.warning(
                    "Extracted subgoal %s does not typecheck as sorry — rejecting sketch",
                    goal.name,
                )
                return DecompositionResult.failure(
                    f"Extracted subgoal `{goal.name}` has a malformed type that does not "
                    f"typecheck even with sorry. The proof sketch likely introduced terms "
                    f"(e.g. Nat.rec, match) that produce ill-typed subgoals. "
                    f"Please use a different decomposition strategy."
                )

        # We have the goal state, and the goals
        # The index of the goal represents its site id and the goals are in order.
        # We want to try out a few things here to remove the trivial goals.
        # For the ones we can knock out with automation, we do it, and for the rest, we
        # prepare the sketch by replace the sorry with the invocation of that goal.
        subgoals  = []
        assembled_sketch = proof_sketch_with_expose
        for goal in goals:
            goal = await self._sanitize_extracted_goal_for_replay(
                pantograph=pantograph,
                goal=goal,
                assembled_sketch=assembled_sketch,
            )

            #
            new_ctx = ctx.copy_with(
                goal=goal
            )
            automation_res = await self._try_automation_with_proof_search(new_ctx)
            if automation_res.success:
                assembled_sketch = replace_first_sorry_with_multiline_tactic(
                    assembled_sketch,
                    automation_res.applied_tactic,
                )
            else:
                # Rename the goal so that it looks cleaner
                # The extract_subgoals call would already have them in order, but since
                # some of them get knocked out by automation, we rename so that we don't
                # get goal_0, goal_3 ..., we want uniformly goal_0,goal_1..goal_n
                goal.name = f"{parent_name}_{len(subgoals)}"
                subgoals.append(SubgoalInfo(goal=goal, has_sorry=True))
                assembled_sketch = replace_first_sorry_with_multiline_tactic(
                    assembled_sketch,
                    exact_goal(goal),
                )

        return DecompositionResult(subgoals=subgoals, assembled_sketch=assembled_sketch)

    @staticmethod
    def _build_subgoal_replay_probe(goal, assembled_sketch: str) -> str:
        """Build a temporary file that probes whether a subgoal invocation replays."""
        invocation_sketch = replace_first_sorry_with_multiline_tactic(
            assembled_sketch,
            exact_goal(goal),
        )
        return f"{goal.as_sorried()}\n\n{invocation_sketch}"

    @staticmethod
    def _unknown_replay_params(goal, diagnostics: list) -> list[str]:
        """Return extracted params that Lean rejects as unknown at replay time."""
        param_names = {param.name for param in goal.params}
        unknown_names: list[str] = []
        for diagnostic in diagnostics:
            if diagnostic.severity != "error":
                continue
            match = UNKNOWN_IDENTIFIER_RE.search(diagnostic.message)
            if match is None:
                continue
            name = match.group(1)
            if name in param_names and name not in unknown_names:
                unknown_names.append(name)
        return unknown_names

    @staticmethod
    async def _sanitize_extracted_goal_for_replay(
        *,
        pantograph: PantographClient,
        goal,
        assembled_sketch: str,
    ):
        """Drop extracted params that are not replayable at the parent call site."""
        current_goal = goal

        while True:
            replay_probe = ProverAgent._build_subgoal_replay_probe(
                current_goal,
                assembled_sketch,
            )
            replay_build = await pantograph.check_build(replay_probe)
            if replay_build.typechecks:
                return current_goal

            unknown_params = ProverAgent._unknown_replay_params(
                current_goal,
                replay_build.diagnostics,
            )
            if not unknown_params:
                logger.info(
                    "Replay probe for %s failed without removable unknown params; "
                    "keeping extracted signature",
                    current_goal.name,
                )
                return current_goal

            changed = False
            for name in unknown_params:
                candidate_goal = filter_goal_params(current_goal, {name})
                if candidate_goal == current_goal:
                    continue

                candidate_build = await pantograph.check_build(candidate_goal.as_sorried())
                if not candidate_build.typechecks:
                    logger.info(
                        "Keeping replay-unknown param %s in %s because removing it "
                        "breaks the standalone subgoal theorem",
                        name,
                        current_goal.name,
                    )
                    continue

                logger.info(
                    "Dropping replay-unstable param %s from extracted goal %s",
                    name,
                    current_goal.name,
                )
                current_goal = candidate_goal
                changed = True

            if not changed:
                logger.info(
                    "Replay probe for %s still fails after attempted sanitization; "
                    "keeping current extracted signature",
                    current_goal.name,
                )
                return current_goal

    @DBOS.step()
    async def _finalize_proof(
        self,
        ctx: ProvingContext,
        assembled_sketch: str,
        subgoal_proofs: Dict[str, str],
        completely_failed_subgoals: List[str],
    ) -> dict:
        logger.info(f"Finalizing proof for {ctx.goal_name}")

        logger.info(f"  ASSEMBLED SKETCH:\n{'-' * 80}\n{assembled_sketch}\n{'-' * 80}")

        failed_theorems = [
            subgoal_proofs[name]
            for name in completely_failed_subgoals
            if name in subgoal_proofs
        ]
        logger.info(
            f"  SUBGOAL THEOREMS ({len(subgoal_proofs)} total, {len(failed_theorems)} completely failed):"
        )
        for name, proof in subgoal_proofs.items():
            status = (
                "COMPLETELY_FAILED"
                if name in completely_failed_subgoals
                else "PROVEN/PARTIAL"
            )
            logger.info(f"    {name} [{status}]:\n{proof}...")

        final_proof = assembled_sketch

        logger.info(f"  FINAL PROOF:\n{'-' * 80}\n{final_proof}\n{'-' * 80}")

        typecheck_result = await self._get_pantograph(ctx).check_build(assembled_sketch)
        if not typecheck_result.typechecks:
            error = (
                typecheck_result.as_string(["error"])
                or typecheck_result.as_string()
                or typecheck_result.build_log
                or "Assembled proof failed to typecheck with no diagnostics."
            )
            logger.warning(
                "  Final proof assembly for %s failed to typecheck; preserving sorried fallback.\n%s",
                ctx.goal_name,
                error,
            )
            return {
                "success": False,
                "content": "",
                "error": error,
                "proof": self._build_assembly_fallback_proof(
                    ctx,
                    assembled_sketch,
                    typecheck_result,
                ),
            }

        # NOTE: Don't write to file here - _finalize_result handles the file write
        # after unused variable removal

        logger.info(f"  ✓ Final proof typechecks successfully!")
        return {
            "success": True,
            "content": "",  # Content will be set by _finalize_result
            "error": "",
            "proof": final_proof,
        }

    @staticmethod
    def _line_comment_block(content: str) -> str:
        """Format arbitrary text as Lean-safe `--` line comments."""
        lines = content.splitlines() or [""]
        return "\n".join(f"-- {line}" if line else "--" for line in lines)

    @classmethod
    def _build_assembly_fallback_proof(
        cls,
        ctx: ProvingContext,
        assembled_sketch: str,
        build_result: LakeBuildResult,
    ) -> str:
        """Preserve a failed assembled proof as comments after a sorried theorem."""
        diagnostics = (
            build_result.as_string(["error"])
            or build_result.as_string()
            or build_result.build_log
            or "(no diagnostics)"
        ).strip()
        commented_attempt = cls._line_comment_block(
            "\n".join(
                [
                    "ASSEMBLY FALLBACK: attempted assembled proof did not typecheck.",
                    "",
                    "Attempted assembled proof:",
                    assembled_sketch.rstrip(),
                    "",
                    "Diagnostics:",
                    diagnostics,
                ]
            ).rstrip()
        )
        return f"{ctx.goal_theorem}\n\n{commented_attempt}"

    @staticmethod
    def _typecheck_error_feedback(lean_code: str, build_result: LakeBuildResult) -> str:
        """Build a feedback string for a failed typecheck."""
        error_str = build_result.as_string(["error"])
        return f"""PREVIOUS ATTEMPT FAILED TO TYPECHECK:

Your theorem:
```lean
{lean_code}
```

**ERRORS**

{error_str}

Please fix the errors and try again."""

    @staticmethod
    def _validate_theorem_signature(
        complete_theorem: str,
        ctx: ProvingContext,
    ) -> Optional[str]:
        """Validate that a generated theorem matches the expected signature.

        Returns None if valid, or an error message string if invalid.
        """
        from utils.lean_helpers import check_theorem_signature_match

        signature_mismatch_result = check_theorem_signature_match(complete_theorem, ctx.goal_theorem)

        if not signature_mismatch_result.matches:
            logger.warning(f"    ✗ Theorem signature mismatch")
            return f"""THEOREM SIGNATURE MISMATCH:
Expected signature:
{ctx.goal_theorem}

Your signature doesn't match. Please ensure the theorem statement is exactly as specified."""
        logger.info(f"    ✓ Theorem signature verified")
        return None

    def _build_shallow_solve_system_context(
        self,
        ctx: ProvingContext,
        hints: str,
    ) -> str:
        """Build static system context for shallow solve (cacheable).

        This contains all the context that doesn't change between iterations:
        file context, goal, hints, informal reasoning, and instructions.
        """
        file_context = ctx.get_relevant_context()
        context_sections = {
            "Relevant Context": lean_block(file_context),
            "Goal to Prove": lean_block(ctx.goal_theorem),
            "Informal Reasoning for the proof": code_block(ctx.informal_reasoning),
        }

        # Add unified hints from RetrieverAgent
        if hints:
            context_sections["Relevant Hints"] = hints

        instructions = [
            f"Provide a complete, working proof for: `{ctx.goal_name}`",
            "",
            "CRITICAL REQUIREMENTS:",
            f"  - The theorem MUST be named exactly: `{ctx.goal_name}`",
            "  - Provide the COMPLETE theorem with signature and proof",
            "  - Match the exact signature from the goal above",
            "  - Use the hints and theorems provided",
            "  - NO `sorry` allowed - provide complete proof",
            "  - Ensure proper indentation",
            "",
        ]

        return render_prompt(
            create_prompt(
                task=stable(f"Prove the goal: {ctx.goal_name}"),
                sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
                instructions=bullets(instructions, segment=PromptSegment.STABLE),
                closing=stable(
                    f"REMEMBER: Theorem must be named `{ctx.goal_name}` exactly. Provide COMPLETE theorem with NO sorry."
                ),
            )
        ).full_text()

    def _build_shallow_solve_user_message(
        self,
        ctx: ProvingContext,
        feedback: IterationFeedback,
        iteration: int,
    ) -> str:
        """Build dynamic user message for shallow solve iteration.

        This contains only the content that changes between iterations:
        error feedback from previous attempt.
        """
        if iteration == 0:
            return f"Please prove the theorem `{ctx.goal_name}`."

        # Subsequent iterations include error feedback
        parts = [f"⚠️ ATTEMPT #{iteration + 1} - Previous attempt failed"]

        if feedback.error:
            parts.append("")
            parts.append(feedback.error)

        parts.append("")
        parts.append(f"Please fix the errors and provide a corrected proof for `{ctx.goal_name}`.")

        return "\n".join(parts)
