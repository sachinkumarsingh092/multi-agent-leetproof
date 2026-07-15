import json
from typing import Optional
from pathlib import Path

from dbos import DBOS
from langchain_core.messages import HumanMessage
from langgraph.graph import StateGraph, START, END

from agents.agent_state import VelvetAgentState, RetryLimitExceeded, PBTStatus, JudgeVerdict
from agents.base import BaseAgent
from agents.velvet_judge import VelvetJudgeAgent
from tools.common import (
    lean_build_file_helper,
    write_method,
    lean_diagnostics_messages,
)
from utils.validation import validate_output_file
from utils.validation_result import ValidationResult
from utils.differ import Differ
from utils.lean.goals import parse_lean_goals
from utils.lean_helpers import LakeBuildResult
from utils.lean.parser import LeanFile, parse_test_cases
from utils.velvet_types import VelvetMethod
from utils.velvet_helpers import (
    get_pbt_code_snippet,
    get_velvet_method,
    generate_assertions,
    get_pbt_counterexamples,
    format_pbt_feedback,
    run_two_phase_pbt,
    extract_goals_after_loom_solve,
    identity,
    find_wpgen_goals,
    extract_wpgen_target_from_diagnostic,
)
from utils.message_helpers import create_prompt, dynamic, section, stable
from utils.program_state import ProgramBuffer
from utils.shutdown import shutdown_boundary
from logging_config import get_logger
from utils.analytics.velvet_programmer import (
    AttemptMeta,
    AttemptOutcome,
    JudgeResult,
    TypecheckSummary,
    write_attempt_meta,
    write_judge_result,
    write_typecheck_summary,
)
from config.constants import BUGS_DIR
from config.limits import Limits
from providers import ReasoningLevel

# Import judge for internal use - avoid circular import by importing class only
from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from agents.velvet_judge import VelvetJudgeAgent
    from providers import LLMConfig

logger = get_logger(__name__)

# Prompt constants
LEAN_LSP_TOOLS = """**Lean LSP Tools Available:**
- `lean_diagnostics_messages`: Get pretty-printed LSP diagnostics filtered by severity (error/warning/info/all, default error)
  Use this to debug type errors and other compilation issues."""

WRITE_METHOD_RULES = """- Use the `write_method` tool to write ONLY your method implementation
- The tool will automatically place it in the Impl section (other sections are preserved)
- Output ONLY the method (signature + body), NOT imports or other sections
- Do NOT call write_method multiple times
- After writing, immediately respond with ONLY the text 'Done' and make NO MORE TOOL CALLS"""

WPGEN_BUG_FEEDBACK_HEADER = """VELVET BUG DETECTED (WPGen goal target)
======================================
Your program typechecks, but the loom_solve goal extraction found goal targets that start with `WPGen`.
This typically indicates a Velvet backend bug rather than a normal proof obligation.

Please rewrite the program in a different style to avoid this bug.
This often happens when `match` and `while` are combined in the same control flow.
Try writing it differently to avoid that combination.
"""


@DBOS.dbos_class()
class VelvetProgrammerAgent(BaseAgent):
    """Agent that generates Velvet programs from specifications and iteratively fixes type errors."""

    name = "velvet_programmer"
    description = "Generates Velvet/Lean programs from specifications and fixes type errors iteratively"

    system_prompt: str = ""
    max_attempts: int = Limits.VELVET_PROGRAMMER_MAX_ATTEMPTS
    max_judge_rejections: int = Limits.MAX_JUDGE_REJECTIONS_PER_AGENT

    additional_context_files = ["prompts/velvet_documentation.md"]

    def __init__(
        self,
        config: "LLMConfig",
        *,
        judge: "VelvetJudgeAgent",
        max_attempts: int = Limits.VELVET_PROGRAMMER_MAX_ATTEMPTS,
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self.max_attempts = max_attempts
        self.judge = judge

        from utils.prompt_helpers import load_system_prompt
        self.system_prompt = load_system_prompt(
            "velvet_programmer.md",
            "You are a Velvet programming expert. Generate correct Lean/Velvet code from specifications.",
        )
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    async def get_tools(self) -> list:
        return [write_method, lean_diagnostics_messages]

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state, {"recursion_limit": 50})

    def build_graph(self) -> StateGraph:
        """Build the generate -> typecheck -> judge loop graph."""

        builder = StateGraph(VelvetAgentState)

        # Generation and typecheck nodes
        builder.add_node("generate", self._generate_node)
        builder.add_node("repair_and_typecheck", self._repair_and_typecheck_node)
        builder.add_node("check_wpgen_bug", self._check_wpgen_bug_node)

        # Judge nodes
        builder.add_node("judge", self._judge_node)
        builder.add_node("setup_retry_after_judge", self._setup_retry_after_judge_node)

        # Generation flow
        builder.add_edge(START, "generate")
        builder.add_edge("generate", "repair_and_typecheck")
        builder.add_conditional_edges(
            "repair_and_typecheck",
            self._should_run_wpgen_bug_check,
            {"retry": "generate", "check": "check_wpgen_bug"},
        )
        builder.add_conditional_edges(
            "check_wpgen_bug",
            self._should_continue_after_wpgen_bug_check,
            {"retry": "generate", "judge": "judge"},
        )

        # Judge flow
        builder.add_conditional_edges(
            "judge",
            self._should_continue_after_judge,
            {"retry": "setup_retry_after_judge", "done": END},
        )
        builder.add_edge("setup_retry_after_judge", "generate")

        return builder

    def _select_reasoning_level(self, attempt_index: int) -> "ReasoningLevel":
        """Escalate programmer reasoning across retry thirds."""
        one_third = max(1, self.max_attempts // 3)
        two_thirds = max(one_third + 1, (2 * self.max_attempts) // 3)

        if attempt_index < one_third:
            return ReasoningLevel.NONE
        if attempt_index < two_thirds:
            return ReasoningLevel.LOW
        return ReasoningLevel.MEDIUM

    def _current_attempt_reasoning_level(self, state: VelvetAgentState) -> "ReasoningLevel":
        """Return the reasoning level used for the current attempt."""
        attempt_index = max(0, state["attempt"] - 1)
        return self._select_reasoning_level(attempt_index)

    @staticmethod
    def _has_assertion_failure(diagnostics: list) -> bool:
        """Detect deterministic assertion failures from error diagnostics."""
        return any(
            diagnostic.severity == "error"
            and "Failed to prove assertion without names:" in diagnostic.message
            for diagnostic in diagnostics
        )

    def _record_typecheck_analytics(
        self,
        state: VelvetAgentState,
        build_result: LakeBuildResult,
        pbt_status: PBTStatus | None = None,
    ) -> None:
        """Store the programmer typecheck/build summary for one attempt."""
        pbt_counterexamples = get_pbt_counterexamples(build_result.diagnostics)
        pbt_failure = bool(pbt_counterexamples)
        assertion_failure = self._has_assertion_failure(build_result.diagnostics)
        passed = build_result.typechecks and not pbt_failure

        program_text = ProgramBuffer.from_dict(state["program_state"]).get_current()
        impl_text = LeanFile.from_content(program_text).get_section(
            "Impl", assert_exists=True
        ).full_text()

        payload = TypecheckSummary(
            build_passed=build_result.typechecks,
            pbt_failure=pbt_failure,
            assertion_failure=assertion_failure,
            program=program_text,
            impl_section=impl_text,
            pbt_status=pbt_status,
            pbt_failure_message=(
                "\n".join(diagnostic.message for diagnostic in pbt_counterexamples)
                if pbt_failure
                else None
            ),
        )

        attempt_log = self._analytics_attempt(state)
        write_typecheck_summary(
            attempt_log,
            payload,
            text=(
                format_pbt_feedback(pbt_counterexamples)
                if pbt_failure
                else build_result.as_string(["error", "warning", "info"])
            ),
        )

        if not passed:
            write_attempt_meta(
                attempt_log,
                AttemptMeta(
                    final_outcome=(
                        AttemptOutcome.PBT_FAILURE
                        if pbt_failure
                        else AttemptOutcome.ASSERTION_FAILURE
                        if assertion_failure
                        else AttemptOutcome.BUILD_FAILURE
                    ),
                    reasoning_level=self._current_attempt_reasoning_level(state).value,
                    file_path=state["output_file"]
                ),
            )

    def _record_judge_analytics(
        self,
        state: VelvetAgentState,
        *,
        verdict: JudgeVerdict,
        reasoning: str,
    ) -> None:
        """Store the judged program, verdict, and reasoning for one attempt."""
        judge_passed = verdict == JudgeVerdict.PASS
        attempt_log = self._analytics_attempt(state)
        write_judge_result(
            attempt_log,
            JudgeResult(
                verdict=verdict,
                reasoning=reasoning,
                program=ProgramBuffer.from_dict(state["program_state"]).get_current(),
            ),
        )
        write_attempt_meta(
            attempt_log,
            AttemptMeta(
                final_outcome=(
                    AttemptOutcome.JUDGE_PASS if judge_passed else AttemptOutcome.JUDGE_FAIL
                ),
                reasoning_level=self._current_attempt_reasoning_level(state).value,
                file_path=state["output_file"]
            ),
        )

    @shutdown_boundary("before programmer generate step")
    @DBOS.step()
    async def _generate_node(self, state: VelvetAgentState) -> dict:
        """Generate or refine the Velvet program using LLM with tools."""
        attempt = state["attempt"] + 1
        logger.info(f"Attempt {attempt}/{self.max_attempts}")

        # Prepare output file with spec content (ensures file exists with all sections)
        output_path = Path(state["output_file"])
        if not output_path.exists():
            logger.info(f"Preparing output file with spec content: {output_path}")
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(state["specification"])

        # Build fresh messages for this invocation
        messages = []
        self.ensure_system_messages(messages)

        if state["attempt"] == 0:
            # First attempt
            context_sections = {"Specification": state["specification"]}

            if state.get("judge_reasoning"):
                context_sections["Judge Feedback from Previous Attempt"] = (
                    state["judge_reasoning"]
                    + "\n\nThe judge evaluated your previous attempt and found issues. Please address the feedback above."
                )

            if state.get("continuation_ctx"):
                context_sections = {
                    **context_sections,
                    **state.get("continuation_ctx", {}),
                }

            prompt = create_prompt(
                task=stable("Please generate a Velvet/Lean program for the following specification:"),
                sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
                instructions=stable(f"""{LEAN_LSP_TOOLS}

The output file should be written to: {state["output_file"]}

**CRITICAL INSTRUCTION:**
{WRITE_METHOD_RULES}"""),
                closing=stable("Focus on correctness and type safety. The code must typecheck."),
            )
        else:
            # Retry: Build a self-sufficient message with all necessary context
            buffer = ProgramBuffer.from_dict(state["program_state"])
            current_impl = LeanFile.from_content(
                buffer.get_current()
            ).get_section("Impl", assert_exists=True).content
            stable_context_sections = {
                "Original Task": "Generate a Velvet/Lean program for the specification below",
                "Specification": state["specification"],
            }
            dynamic_context_sections = {
                "Current Implementation (with errors)": current_impl,
                "Build Errors": state["build_log"],
            }

            if state.get("judge_reasoning"):
                dynamic_context_sections["Judge Feedback from Previous Attempt"] = (
                    state["judge_reasoning"]
                    + "\n\nThe judge evaluated your previous attempt and found issues. Please address the feedback above."
                )

            if state.get("continuation_ctx"):
                stable_context_sections = {
                    **stable_context_sections,
                    **state.get("continuation_ctx", {}),
                }

            prompt_sections = tuple(
                section(k, stable(v)) for k, v in stable_context_sections.items()
            ) + tuple(
                section(k, dynamic(v)) for k, v in dynamic_context_sections.items()
            ) + (
                section(
                    "Issues To Address",
                    dynamic("The previous program had issues. Please fix them."),
                ),
            )
            prompt = create_prompt(
                task=stable("Please generate a Velvet/Lean program for the following specification:"),
                sections=prompt_sections,
                instructions=stable(f"""{LEAN_LSP_TOOLS}

The output file should be written to: {state["output_file"]}

**CRITICAL INSTRUCTION:**
{WRITE_METHOD_RULES}"""),
                closing=stable("Focus on correctness and type safety. The code must typecheck."),
            )

        self.append_prompt(messages, prompt)

        # Invoke LLM with tools (messages accumulate internally, but we don't persist them)
        response = await self.invoke_with_tools(
            messages,
            max_iterations=Limits.VELVET_PROGRAMMER_MAX_ITERATIONS,
            reasoning_level=self._select_reasoning_level(state["attempt"]),
        )

        # Read the file that was written to get the program
        if state["output_file"] and Path(state["output_file"]).exists():
            program = Path(state["output_file"]).read_text()
        else:
            program = response.content
            logger.warning("Output file not found, using LLM response content directly")

        return {
            "program_state": ProgramBuffer.from_dict(state["program_state"]).update_current(
                program
            ),
            "attempt": state["attempt"] + 1,
        }

    def _try_add_pbt(
        self,
        output_file: str,
    ) -> tuple[PBTStatus, LakeBuildResult | None, dict | None]:
        """Try to add PBT section after successful typecheck."""
        logger.info("Attempting to add PBT section")
        lean_file = LeanFile.from_path(output_file)
        impl_section = lean_file.get_section("Impl", assert_exists=True)
        method = get_velvet_method(impl_section.content)

        return run_two_phase_pbt(
            output_file,
            lambda max_ms: get_pbt_code_snippet(method, max_ms=max_ms),
            compile_failure_comment="Decidable instance synthesis failed for this method's conditions. Giving up on PBT.",
            log_prefix="PBT",
        )

    @shutdown_boundary("before programmer typecheck step")
    @DBOS.step()
    def _repair_and_typecheck_node(self, state: VelvetAgentState) -> dict:
        """Run lake build to typecheck the program.

        Flow:
        1. Validate output structure
        2. Generate Assertions section (deterministic)
        3. Typecheck
        4. Check for PBT counterexamples → if found, return as feedback
        5. If build fails → return errors
        6. If build passes and pbt_status is NOT_ATTEMPTED → add PBT, typecheck again
        """
        logger.info("Running typecheck")

        # 1. Validate output file exists
        is_valid, error_state = validate_output_file(state)
        if not is_valid:
            return error_state

        # 2. Validate output structure (signature unchanged, etc.)
        buffer = ProgramBuffer.from_dict(state["program_state"])
        validation_result = validate_programmer_output(
            state["specification"], buffer.get_current()
        )
        if validation_result.has_error():
            logger.warning(
                f"Programmer output validation failed: {validation_result.get_error()}"
            )
            return {"typechecks": False, "build_log": validation_result.get_error()}
        logger.info(
            "Output validation passed (sections preserved, signature unchanged)"
        )

        # 3. Generate Assertions section (deterministic)
        lean_file = LeanFile.from_path(state["output_file"])
        impl_section = lean_file.get_section("Impl", assert_exists=True)
        testcases_section = lean_file.get_section("TestCases", assert_exists=True)

        method = get_velvet_method(impl_section.content)
        test_cases = parse_test_cases(testcases_section.content, method)

        if not test_cases:
            raise ValueError("No test cases found in TestCases section")

        assertions_content = generate_assertions(method, test_cases)
        lean_file.add_or_replace_section(
            "Assertions", assertions_content, after="TestCases"
        )
        lean_file.reconstruct_and_write_to_file(Path(state["output_file"]))
        logger.info(f"Generated Assertions section with {len(test_cases)} test cases")

        # 4. Typecheck (include_info_logs=True to capture PBT FAIL messages which are info severity)
        result = lean_build_file_helper(state["output_file"], include_info_logs=True)
        analytics_build_result = result
        existing_pbt_status = state.get("pbt_status", PBTStatus.NOT_ATTEMPTED)
        analytics_pbt_status = (
            existing_pbt_status
            if existing_pbt_status != PBTStatus.NOT_ATTEMPTED
            else None
        )

        # 5. Check for PBT counterexamples in diagnostics
        counterexamples = get_pbt_counterexamples(result.diagnostics)
        if counterexamples:
            feedback = format_pbt_feedback(counterexamples)
            logger.warning(f"PBT found {len(counterexamples)} counterexamples")
            final_result = {"typechecks": False, "build_log": feedback}
        elif not result.typechecks:
            # 6. Build failed without the PBT counterexample path above
            final_result = {"typechecks": False, "build_log": result.as_string(["error"])}
        else:
            # 7. Build passed - try adding PBT if not tried yet
            pbt_status = existing_pbt_status
            if pbt_status == PBTStatus.NOT_ATTEMPTED:
                pbt_status, pbt_build_result, pbt_result = self._try_add_pbt(state["output_file"])
                analytics_pbt_status = pbt_status
                if pbt_build_result is not None:
                    analytics_build_result = pbt_build_result

                if pbt_result:
                    final_result = {**pbt_result, "pbt_status": pbt_status}
                else:
                    program = Path(state["output_file"]).read_text()
                    final_result = {
                        "typechecks": True,
                        "build_log": result.as_string(["error"]),
                        "pbt_status": pbt_status,
                        "program_state": buffer.update_current(
                            program,
                            promote_to_stable=True,
                        ),
                        **self._save_phase_result(state, program),
                    }
            else:
                program = Path(state["output_file"]).read_text()
                final_result = {
                    "typechecks": True,
                    "build_log": result.as_string(["info", "warning"]),
                    "program_state": buffer.update_current(
                        program,
                        promote_to_stable=True,
                    ),
                    **self._save_phase_result(state, program),
                }

        self._record_typecheck_analytics(
            state,
            analytics_build_result,
            pbt_status=analytics_pbt_status,
        )
        return final_result

    @shutdown_boundary("before programmer wpgen-check step")
    @DBOS.step()
    async def _check_wpgen_bug_node(self, state: VelvetAgentState) -> dict:
        """Detect Velvet WPGen bug patterns in loom_solve goals.

        If any extracted goal target starts with `WPGen`, we treat it as a
        backend bug trigger and force a retry with targeted feedback.
        """
        if not state.get("typechecks"):
            return {}

        buffer = ProgramBuffer.from_dict(state["program_state"])
        program = buffer.get_current()
        output_file = state["output_file"]

        try:
            goal_result_str, _ = await extract_goals_after_loom_solve(
                program,
                output_file,
                preprocess=identity,
                postprocess=identity,
            )
        except Exception as e:
            logger.warning(f"WPGen bug check failed, skipping check: {e}")
            return {}

        goals = parse_lean_goals(goal_result_str) if goal_result_str.strip() else []
        wpgen_goals = find_wpgen_goals(goals)
        raw_wpgen_target = extract_wpgen_target_from_diagnostic(goal_result_str)

        if not wpgen_goals and not raw_wpgen_target:
            return {}

        bug_report_dir = self._save_wpgen_bug_report(
            state,
            program,
            wpgen_goals,
        )
        feedback = WPGEN_BUG_FEEDBACK_HEADER.strip()

        detected_count = len(wpgen_goals) if wpgen_goals else 1
        logger.warning(
            f"Detected {detected_count} WPGen goal(s); forcing retry. "
            f"Bug report saved to {bug_report_dir}"
        )

        continuation_ctx = {
            **state.get("continuation_ctx", {}),
            "Velvet WPGen Detection Feedback": feedback,
        }

        return {
            "typechecks": False,
            "build_log": feedback,
            "continuation_ctx": continuation_ctx,
        }

    def _get_session_id_for_bug_report(self) -> str:
        """Get DBOS workflow/session id for bug report paths.

        This is replay-safe inside DBOS steps and reflects retry workflow IDs
        (e.g., session_retry1) when forking/resuming.
        """
        workflow_id = DBOS.workflow_id
        return workflow_id or "unknown_session"

    def _save_wpgen_bug_report(
        self,
        state: VelvetAgentState,
        program: str,
        wpgen_goals: list,
    ) -> str:
        """Persist bug snapshot for later Velvet debugging."""
        session_id = self._get_session_id_for_bug_report()
        output_stem = Path(state["output_file"]).stem
        attempt = state.get("attempt", 0)
        bug_id = f"{output_stem}_attempt{attempt}"

        bug_dir = Path(BUGS_DIR) / session_id / bug_id
        bug_dir.mkdir(parents=True, exist_ok=True)

        program_path = bug_dir / Path(state["output_file"]).name
        program_path.write_text(program)

        goals_payload = [
            {
                "name": g.name,
                "case_tag": g.case_tag,
                "target": g.final_goal,
                "theorem": g.as_theorem(),
            }
            for g in wpgen_goals
        ]

        payload = {
            "agent": self.name,
            "session_id": session_id,
            "output_file": state.get("output_file"),
            "attempt": state.get("attempt"),
            "note": (
                "Detected goal target(s) that start with WPGen after loom_solve. "
                "This is likely a Velvet backend bug."
            ),
            "likely_trigger": "Combination of match and while in control flow",
            "wpgen_goals": goals_payload,
            "build_log_before_bug_check": state.get("build_log", ""),
        }
        (bug_dir / "bug_report.json").write_text(json.dumps(payload, indent=2))

        return str(bug_dir)

    # NOTE: This is a @DBOS.step() that calls judge.evaluate (also a step),
    # creating a step-in-step where evaluate isn't independently checkpointed.
    # This is acceptable because: (1) the only code after evaluate() is trivial
    # dict construction that can't fail, so the inner step is never wasted, and
    # (2) removing @DBOS.step() here would expose the LeanFile.from_path() file
    # read to the workflow body — on replay, prior steps return cached without
    # re-executing their file writes, so the file would be stale.
    @shutdown_boundary("before programmer judge step")
    @DBOS.step()
    async def _judge_node(self, state: VelvetAgentState) -> dict:
        """Evaluate the output using judge with caching optimization."""
        logger.info("Running judge evaluation")

        lean_file = LeanFile.from_path(state["output_file"])
        specs_section = lean_file.get_section("Specs")
        impl_section = lean_file.get_section("Impl", assert_exists=True)

        # Static context: docs (shared across programmer/inferrer - cached)
        static_ctx = self._get_additional_context()

        # Dynamic context: changes per evaluation
        dynamic_ctx = {
            "Build Status": f"Build Passed: {state['typechecks']}",
            "Build Log": "No Build Errors Detected" if state["typechecks"] else state["build_log"],
            "Specification": specs_section.content if specs_section else "(not available)",
            "Output produced by the Agent": impl_section.content,
        }

        verdict, reasoning = await self.judge.evaluate(
            agent_name=self.name,
            agent_system_prompt=self.system_prompt,
            dynamic_ctx=dynamic_ctx,
            static_ctx=static_ctx,
        )

        self._record_judge_analytics(
            state,
            verdict=verdict,
            reasoning=reasoning,
        )

        result = {
            "judge_verdict": verdict,
            "judge_reasoning": reasoning,
            "messages": [],  # Clear messages for fresh start
        }

        # Track rejections
        if verdict == JudgeVerdict.FAIL:
            rejections_dict = dict(state.get("judge_rejections", {}))
            current = rejections_dict.get(self.name, 0)
            rejections_dict[self.name] = current + 1
            result["judge_rejections"] = rejections_dict
            logger.info(f"Judge rejected {self.name} (rejection #{rejections_dict[self.name]})")

        return result

    @shutdown_boundary("before programmer retry-after-judge step")
    @DBOS.step()
    def _setup_retry_after_judge_node(self, state: VelvetAgentState) -> dict:
        """Set up state for retry after judge rejection."""
        logger.info("Setting up retry after judge rejection")

        lean_file = LeanFile.from_path(state["output_file"])
        impl_section = lean_file.get_section("Impl", assert_exists=True)

        # Store rejected impl in continuation_ctx for next attempt
        return {
            "continuation_ctx": {
                "Implementation Judged by the Judge": impl_section.content
            },
        }

    def _should_run_wpgen_bug_check(self, state: VelvetAgentState) -> str:
        """Route after typecheck: retry on failure, else run WPGen bug check."""
        if state.get("typechecks"):
            return "check"
        if state["attempt"] >= self.max_attempts:
            logger.error(f"Max attempts ({self.max_attempts}) reached without success")
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=self.max_attempts,
                reason="Failed to generate typechecking code",
            )
        return "retry"

    def _should_continue_after_wpgen_bug_check(self, state: VelvetAgentState) -> str:
        """Route after WPGen bug check: retry on bug, otherwise go to judge."""
        if state.get("typechecks"):
            return "judge"
        if state["attempt"] >= self.max_attempts:
            logger.error(f"Max attempts ({self.max_attempts}) reached without success")
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=self.max_attempts,
                reason="Failed to generate typechecking code",
            )
        return "retry"

    def _should_continue_after_judge(self, state: VelvetAgentState) -> str:
        """Determine whether to retry after judge or finish."""
        if state.get("judge_verdict") == JudgeVerdict.PASS:
            return "done"

        rejections = state.get("judge_rejections", {}).get(self.name, 0)
        if rejections >= self.max_judge_rejections:
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=rejections,
                reason="Judge rejected too many times",
            )
        return "retry"


def main():
    """Entry point for lloom-agent-programmer CLI command."""
    VelvetProgrammerAgent.main()


def validate_programmer_output(old_content: str, new_content: str) -> ValidationResult:
    """Validate output from Programmer agent.

    Required sections: Specs, Impl, TestCases
    Unchanged sections: Specs, TestCases
    Impl section: signature unchanged, only body changed
    """
    required = ["Specs", "Impl", "TestCases"]
    unchanged = ["Specs", "TestCases"]

    try:
        old_file = LeanFile.from_content(old_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse old content as LeanFile: {e}")

    try:
        new_file = LeanFile.from_content(new_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse new content as LeanFile: {e}")

    # Check required sections exist
    missing = [s for s in required if not new_file.has_section(s)]
    if missing:
        return ValidationResult.error(
            f"Output missing required sections: {missing}\n"
            f"Found sections: {new_file.section_names()}"
        )

    # Check unchanged sections
    for section_name in unchanged:
        d = Differ(
            f"old:{section_name}",
            old_file.get_section(section_name, assert_exists=True).content.strip(),
            f"new:{section_name}",
            new_file.get_section(section_name, assert_exists=True).content.strip(),
        )
        if not d.is_empty():
            return ValidationResult.error(
                f"Found modified section '{section_name}', which should be unchanged.\n"
                f"Diff:\n{d.format()}"
            )

    # Validate Impl section: signature unchanged, only body changed
    old_impl = old_file.get_section("Impl", assert_exists=True).content
    new_impl = new_file.get_section("Impl", assert_exists=True).content

    try:
        old_method = get_velvet_method(old_impl)
    except Exception as e:
        return ValidationResult.error(f"Failed to parse old Impl as VelvetMethod: {e}")

    try:
        new_method = get_velvet_method(new_impl)
    except Exception as e:
        return ValidationResult.error(f"Failed to parse new Impl as VelvetMethod: {e}")

    # Check signature is unchanged
    if not _signature_unchanged(old_method, new_method):
        d = Differ("old:Impl", old_impl.strip(), "new:Impl", new_impl.strip())
        return ValidationResult.error(
            f"Method signature change detected.\nFull Impl diff:\n{d.format()}"
        )

    return ValidationResult.ok()


def _build_pbt_pass_comment(diagnostics) -> str:
    """Build a comment string summarizing PBT results after a successful run.

    Includes the test count from the PASS message and any items that were skipped
    due to missing Decidable/Testable instances.
    """
    import re

    pass_count = None
    skipped_items = []

    for d in diagnostics:
        if d.severity == "info":
            m = re.search(r'\[velvet_plausible_test\] PASS: (\d+) tests passed', d.message)
            if m:
                pass_count = int(m.group(1))
        elif d.severity == "warning" and "skipping" in d.message:
            # Extract what was skipped, e.g. "postcondition' A res"
            m = re.search(r'for:\s*\n?\s*(.+)', d.message)
            if m:
                skipped_items.append(m.group(1).strip())

    lines = []
    count_str = f"{pass_count:,}" if pass_count is not None else "all"
    lines.append(f"PBT passed: {count_str} tests succeeded.")
    if skipped_items:
        lines.append("The following were not tested (could not synthesize Decidable/Testable):")
        for i, item in enumerate(skipped_items, 1):
            lines.append(f"  {i}. {item}")
    return "\n".join(lines)


def _signature_unchanged(old: VelvetMethod, new: VelvetMethod) -> bool:
    """Check if method signature is unchanged."""
    return (
        old.name == new.name
        and old.params == new.params
        and old.returns == new.returns
        and old.requires == new.requires
        and old.ensures == new.ensures
    )


if __name__ == "__main__":
    main()
