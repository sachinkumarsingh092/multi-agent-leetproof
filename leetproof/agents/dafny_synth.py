"""Dafny Synthesis Agent.

This agent synthesizes verified Dafny programs from Lean specifications.

The flow is:
1. Parse Lean spec to extract specification (precondition/postcondition) and test cases
2. Generate Dafny program using LLM
3. Verify and run using `dafny run --target:py`
4. If errors, feed back for next iteration
5. If no errors, pass to judge for validation
6. If judge passes, done. If judge rejects, retry with feedback.
"""

import re
import subprocess
from dataclasses import dataclass
from typing import Optional, TYPE_CHECKING
from pathlib import Path

from dbos import DBOS

if TYPE_CHECKING:
    from agents.velvet_judge import VelvetJudgeAgent
    from providers import LLMConfig, ReasoningLevel

from langchain_core.messages import HumanMessage
from langgraph.graph import StateGraph, START, END
from providers import ReasoningLevel

from agents.agent_state import VelvetAgentState, RetryLimitExceeded, JudgeVerdict
from agents.base import BaseAgent
from config.limits import Limits
from utils.lean.parser import LeanFile
from logging_config import get_logger
from utils.message_helpers import create_prompt, dynamic, section, stable
from utils.program_state import ProgramBuffer

logger = get_logger(__name__)


# --- Constants ---

DAFNY_SYNTH_MAX_ATTEMPTS = 15
DAFNY_SYNTH_MAX_JUDGE_REJECTIONS = 7


@dataclass
class DafnyBuildResult:
    """Result from running Dafny verification/execution."""
    success: bool
    output: str
    errors: str

    def as_string(self) -> str:
        """Return combined output and errors."""
        parts = []
        if self.output:
            parts.append(f"Output:\n{self.output}")
        if self.errors:
            parts.append(f"Errors:\n{self.errors}")
        return "\n\n".join(parts) if parts else "No output"


def run_dafny(file_path: str, timeout: int = 120) -> DafnyBuildResult:
    """Run Dafny verification and execution on a file.

    Uses `dafny run --target:py` to verify and execute the program.

    Args:
        file_path: Path to the .dfy file
        timeout: Timeout in seconds

    Returns:
        DafnyBuildResult with success status and output/errors
    """
    try:
        result = subprocess.run(
            ["dafny", "run", "--target:py", file_path],
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        success = result.returncode == 0
        return DafnyBuildResult(
            success=success,
            output=result.stdout,
            errors=result.stderr,
        )
    except subprocess.TimeoutExpired:
        return DafnyBuildResult(
            success=False,
            output="",
            errors=f"Dafny execution timed out after {timeout} seconds",
        )
    except FileNotFoundError:
        return DafnyBuildResult(
            success=False,
            output="",
            errors="Dafny not found. Please ensure Dafny is installed and in PATH.",
        )
    except Exception as e:
        return DafnyBuildResult(
            success=False,
            output="",
            errors=f"Error running Dafny: {str(e)}",
        )


def extract_specs_and_tests(lean_content: str) -> tuple[str, str]:
    """Extract Specs and TestCases sections from Lean content.

    Args:
        lean_content: The full Lean specification file content

    Returns:
        Tuple of (specs_content, testcases_content)
    """
    try:
        lean_file = LeanFile.from_content(lean_content)
        specs_section = lean_file.get_section("Specs")
        testcases_section = lean_file.get_section("TestCases")

        specs_content = specs_section.content if specs_section else ""
        testcases_content = testcases_section.content if testcases_section else ""

        return specs_content, testcases_content
    except Exception as e:
        logger.warning(f"Could not parse Lean file sections: {e}")
        # Fallback: return the whole content as specs
        return lean_content, ""


def extract_problem_description(lean_content: str) -> str:
    """Extract the problem description comment from Lean content.

    Looks for /- Problem Description ... -/ block.

    Args:
        lean_content: The full Lean specification file content

    Returns:
        Problem description string, or empty if not found
    """
    import re

    # Match /- Problem Description ... -/
    pattern = r'/\-\s*Problem Description\s*(.*?)\-/'
    match = re.search(pattern, lean_content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return ""


# --- Agent ---

@DBOS.dbos_class()
class DafnySynthAgent(BaseAgent):
    """Agent that synthesizes verified Dafny programs from Lean specifications."""

    name = "dafny_synth"
    description = "Synthesizes verified Dafny programs from Lean specifications"

    system_prompt: str = ""
    max_attempts: int = DAFNY_SYNTH_MAX_ATTEMPTS
    max_judge_rejections: int = DAFNY_SYNTH_MAX_JUDGE_REJECTIONS

    def __init__(
        self,
        config: "LLMConfig",
        *,
        judge: "VelvetJudgeAgent",
        max_attempts: int = DAFNY_SYNTH_MAX_ATTEMPTS,
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self.max_attempts = max_attempts
        self.judge = judge
        from utils.prompt_helpers import load_system_prompt

        self.system_prompt = load_system_prompt(
            "dafny_synthesizer.md",
            "You are a Dafny programming expert. Generate correct verified Dafny programs from Lean specifications.",
        )

        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    async def get_tools(self) -> list:
        """No tools for this agent - we handle file writes and verification manually."""
        return []

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state, {"recursion_limit": 50})

    def build_graph(self) -> StateGraph:
        """Build the synthesis graph."""
        builder = StateGraph(VelvetAgentState)

        # Nodes
        builder.add_node("generate", self._generate_node)
        builder.add_node("verify_and_run", self._verify_and_run_node)
        builder.add_node("judge", self._judge_node)
        builder.add_node("setup_retry_after_judge", self._setup_retry_after_judge_node)

        # Flow
        builder.add_edge(START, "generate")
        builder.add_edge("generate", "verify_and_run")
        builder.add_conditional_edges(
            "verify_and_run",
            self._should_continue_after_verify,
            {"retry": "generate", "judge": "judge"},
        )
        builder.add_conditional_edges(
            "judge",
            self._should_continue_after_judge,
            {"retry": "setup_retry_after_judge", "done": END},
        )
        builder.add_edge("setup_retry_after_judge", "generate")

        return builder

    def _select_reasoning_level(self, attempt_index: int) -> "ReasoningLevel":
        """Escalate synthesis reasoning across retry thirds."""
        one_third = max(1, self.max_attempts // 3)
        two_thirds = max(one_third + 1, (2 * self.max_attempts) // 3)

        if attempt_index < one_third:
            return ReasoningLevel.NONE
        if attempt_index < two_thirds:
            return ReasoningLevel.LOW
        return ReasoningLevel.MEDIUM

    @DBOS.step()
    async def _generate_node(self, state: VelvetAgentState) -> dict:
        """Generate or refine the Dafny program using LLM."""
        attempt = state["attempt"] + 1
        logger.info(f"{'='*60}")
        logger.info(f"Dafny synthesis attempt {attempt}/{self.max_attempts}")
        logger.info(f"{'='*60}")

        # Extract specs and test cases from the Lean specification
        specs_content, testcases_content = extract_specs_and_tests(state["specification"])
        problem_desc = extract_problem_description(state["specification"])

        # Log extracted content
        if problem_desc:
            logger.info("Problem description found")
        logger.info(f"Specs content length: {len(specs_content)} chars")
        logger.info(f"Test cases content length: {len(testcases_content)} chars")

        # Build context sections
        context_sections = {}

        if problem_desc:
            context_sections["Problem Description"] = problem_desc

        context_sections["Lean Specification (to translate)"] = specs_content

        if testcases_content:
            context_sections["Test Cases (from Lean)"] = testcases_content

        # Include previous attempt context if retrying
        if state.get("judge_context"):
            logger.info("Including previous judge-rejected implementation in context")
            context_sections.update(state["judge_context"])

        if state["attempt"] > 0:
            logger.info("Including previous failed implementation and errors in context")
            buffer = ProgramBuffer.from_dict(state["program_state"])
            previous_program = buffer.get_current()
            if previous_program:
                context_sections["Previous Dafny Program (with errors)"] = previous_program
                context_sections["Build/Verification Errors"] = state.get("build_log", "")

        if state.get("judge_reasoning"):
            logger.info("Including judge feedback in context")
            context_sections["Judge Feedback"] = state["judge_reasoning"]

        # Log what context we're providing
        logger.info(f"Context sections provided: {list(context_sections.keys())}")

        # Task description
        task_desc = """Translate the following Lean specification to a verified Dafny program.

Your output must be ONLY the complete Dafny program, with no explanations or markdown.
The program must:
1. Translate the Lean specs to Dafny predicates/functions
2. Implement the `Implementation` method with correct preconditions and postconditions
3. Include proper loop invariants and decreases clauses
4. Enforce total correctness (no `decreases *`)
5. Have a `Main` method with `expect` statements for all test cases"""

        # Closing reminder
        closing = "Output ONLY the Dafny code. No explanations. No markdown code blocks."
        if state.get("judge_reasoning"):
            closing += "\n\nYour previous implementation was rejected by the judge. Address the feedback above."
        elif state["attempt"] > 0:
            closing += "\n\nYour previous implementation had errors. Fix them based on the error messages above."

        prompt = create_prompt(
            task=stable(task_desc),
            sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
            instructions=None,
            closing=(
                dynamic(closing)
                if state.get("judge_reasoning") or state["attempt"] > 0
                else stable(closing)
            ),
        )

        # Fresh messages each time
        messages = []
        self.ensure_system_messages(messages)
        self.append_prompt(messages, prompt)

        # No tools - just get the response
        logger.info("Invoking LLM for Dafny code generation...")
        response = await self.ainvoke_llm(
            messages,
            reasoning_level=self._select_reasoning_level(state["attempt"]),
        )

        # Extract the Dafny code from the response
        dafny_code = self._extract_dafny_code(response.content)

        # Log the generated code
        logger.info(f"{'='*60}")
        logger.info("GENERATED DAFNY CODE:")
        logger.info(f"{'='*60}")
        for i, line in enumerate(dafny_code.split('\n'), 1):
            logger.info(f"{i:4d} | {line}")
        logger.info(f"{'='*60}")

        # Write to output file
        output_path = Path(state["output_file"])
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(dafny_code)
        logger.info(f"Written to: {output_path}")

        return {
            "program_state": ProgramBuffer.from_dict(state["program_state"]).update_current(
                dafny_code
            ),
            "attempt": attempt,
        }

    def _extract_dafny_code(self, content: str) -> str:
        """Extract Dafny code from LLM response.

        Handles cases where the response might be wrapped in markdown code blocks.
        """
        content = content.strip()

        # Remove markdown code blocks if present
        if content.startswith("```dafny"):
            content = content[8:]
        elif content.startswith("```"):
            content = content[3:]

        if content.endswith("```"):
            content = content[:-3]

        return content.strip()

    @DBOS.step()
    def _verify_and_run_node(self, state: VelvetAgentState) -> dict:
        """Verify and run the Dafny program."""
        logger.info(f"{'='*60}")
        logger.info("DAFNY VERIFICATION AND EXECUTION")
        logger.info(f"{'='*60}")
        logger.info(f"File: {state['output_file']}")

        # Enforce total-correctness policy: forbid wildcard decreases.
        current_program = ProgramBuffer.from_dict(state["program_state"]).get_current()
        if re.search(r"^\s*decreases\s+\*\b", current_program, re.MULTILINE):
            msg = (
                "Forbidden termination bypass detected: `decreases *`. "
                "Use explicit decreases clauses for loops/recursion."
            )
            logger.warning(msg)
            return {
                "typechecks": False,
                "build_log": msg,
            }

        result = run_dafny(state["output_file"])

        if result.success:
            logger.info("✅ Dafny verification and execution SUCCEEDED")
            if result.output:
                logger.info(f"Output:\n{result.output}")
            buffer = ProgramBuffer.from_dict(state["program_state"])
            return {
                "typechecks": True,
                "build_log": result.as_string(),
                "program_state": buffer.promote_current(),
            }
        else:
            logger.warning("❌ Dafny verification/execution FAILED")
            logger.warning(f"{'='*60}")
            logger.warning("ERRORS:")
            logger.warning(f"{'='*60}")
            if result.errors:
                for line in result.errors.split('\n'):
                    logger.warning(line)
            if result.output:
                logger.warning(f"{'='*60}")
                logger.warning("OUTPUT:")
                logger.warning(f"{'='*60}")
                for line in result.output.split('\n'):
                    logger.warning(line)
            logger.warning(f"{'='*60}")
            return {
                "typechecks": False,
                "build_log": result.as_string(),
            }

    async def _judge_node(self, state: VelvetAgentState) -> dict:
        """Evaluate the output using judge."""
        logger.info(f"{'='*60}")
        logger.info("JUDGE EVALUATION")
        logger.info(f"{'='*60}")

        # Dynamic context for judge
        dynamic_ctx = {
            "Build Status": f"Build/Verification Passed: {state['typechecks']}",
            "Build Log": state["build_log"] if state["build_log"] else "No errors",
            "Specification (Lean)": state["specification"],
            "Output produced by the Agent (Dafny)": ProgramBuffer.from_dict(
                state["program_state"]
            ).get_current(),
        }

        logger.info("Invoking judge...")
        verdict, reasoning = await self.judge.evaluate(
            agent_name=self.name,
            agent_system_prompt=self.system_prompt,
            dynamic_ctx=dynamic_ctx,
            static_ctx=None,
        )

        # Log verdict and reasoning
        logger.info(f"{'='*60}")
        if verdict == JudgeVerdict.PASS:
            logger.info("✅ JUDGE VERDICT: PASS")
        else:
            logger.info("❌ JUDGE VERDICT: FAIL")
        logger.info(f"{'='*60}")
        logger.info("JUDGE REASONING:")
        logger.info(f"{'='*60}")
        for line in reasoning.split('\n'):
            logger.info(line)
        logger.info(f"{'='*60}")

        result = {
            "judge_verdict": verdict,
            "judge_reasoning": reasoning,
        }

        # Track rejections
        if verdict == JudgeVerdict.FAIL:
            rejections_dict = dict(state.get("judge_rejections", {}))
            current = rejections_dict.get(self.name, 0)
            rejections_dict[self.name] = current + 1
            result["judge_rejections"] = rejections_dict
            result["attempt"] = 0  # Reset attempt counter for next round
            logger.info(f"Total judge rejections for {self.name}: {rejections_dict[self.name]}/{self.max_judge_rejections}")

        return result

    def _setup_retry_after_judge_node(self, state: VelvetAgentState) -> dict:
        """Set up state for retry after judge rejection."""
        logger.info(f"{'='*60}")
        logger.info("SETTING UP RETRY AFTER JUDGE REJECTION")
        logger.info(f"{'='*60}")
        logger.info("Storing rejected implementation for context in next attempt")
        logger.info("Resetting attempt counter to 0")

        # Store rejected impl in judge_context for next attempt
        judge_context = dict(state.get("judge_context", {}))
        judge_context["Previous Implementation (rejected by judge)"] = ProgramBuffer.from_dict(
            state["program_state"]
        ).get_current()

        return {
            "judge_context": judge_context,
            "attempt": 0,  # Reset attempt counter
        }

    def _should_continue_after_verify(self, state: VelvetAgentState) -> str:
        """Decide whether to retry or proceed to judge after verification."""
        if state.get("typechecks"):
            return "judge"
        if state["attempt"] >= self.max_attempts:
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=self.max_attempts,
                reason="Failed to generate verified Dafny code",
            )
        return "retry"

    def _should_continue_after_judge(self, state: VelvetAgentState) -> str:
        """Decide whether to retry or finish after judge evaluation."""
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


async def run_from_spec(
    input_file: str,
    output_file: str,
    agent: Optional["DafnySynthAgent"] = None,
) -> dict:
    """Run Dafny synthesis from a Lean spec file.

    Requires DBOS to be initialized first (via main()).

    Args:
        input_file: Path to the Lean specification file
        output_file: Path for the output Dafny file
        agent: Optional agent instance. If not provided, gets from container.

    Returns:
        Final agent state
    """
    logger.info(f"{'='*60}")
    logger.info("DAFNY SYNTHESIS AGENT")
    logger.info(f"{'='*60}")
    logger.info(f"Input file:  {input_file}")
    logger.info(f"Output file: {output_file}")
    logger.info(f"{'='*60}")

    spec = Path(input_file).read_text()

    # Log the input spec
    logger.info("INPUT SPECIFICATION:")
    logger.info(f"{'='*60}")
    for i, line in enumerate(spec.split('\n'), 1):
        logger.info(f"{i:4d} | {line}")
    logger.info(f"{'='*60}")

    from agents.agent_state import PBTStatus

    state: VelvetAgentState = {
        "specification": spec,
        "program_state": ProgramBuffer.empty(output_file).to_dict(),
        "build_log": "",
        "typechecks": False,
        "attempt": 0,
        "judge_rejections": {},
        "output_file": output_file,
        "judge_verdict": JudgeVerdict.PENDING,
        "judge_reasoning": "",
        "phase_results": {},
        "judge_context": {},
        "goals": [],
        "continuation_ctx": {},
        "pbt_status": PBTStatus.NOT_ATTEMPTED,
    }

    # Use provided agent or get from container
    if agent is None:
        from container import get_container
        container = get_container()
        agent = container.dafny_synth

    final_state = await agent.run_workflow(state)

    # Log final results
    logger.info(f"{'='*60}")
    logger.info("DAFNY SYNTHESIS COMPLETE")
    logger.info(f"{'='*60}")
    logger.info(f"Final verdict: {final_state.get('judge_verdict', 'N/A')}")
    logger.info(f"Typechecks: {final_state.get('typechecks', False)}")
    logger.info(f"Total attempts: {final_state.get('attempt', 0)}")
    logger.info(f"Judge rejections: {final_state.get('judge_rejections', {}).get('dafny_synth', 0)}")
    logger.info(f"{'='*60}")

    buffer = ProgramBuffer.from_dict(final_state["program_state"])
    final_program = buffer.get_stable()
    if final_program:
        logger.info("FINAL DAFNY PROGRAM:")
        logger.info(f"{'='*60}")
        for i, line in enumerate(final_program.split('\n'), 1):
            logger.info(f"{i:4d} | {line}")
        logger.info(f"{'='*60}")

    return final_state


def write_result_json(output_file: str, final_state: dict, session_dir: Optional[Path] = None) -> str:
    """Write result stats to JSON file.

    Args:
        output_file: Path to the output .dfy file
        final_state: Final workflow state
        session_dir: Optional session directory to write result to
    """
    import json

    # Derive result filename from output file
    output_path = Path(output_file)
    if output_file.endswith(".dfy"):
        result_name = output_path.stem + "_result.json"
    else:
        result_name = output_path.name + "_result.json"

    # Put in session directory if provided, otherwise next to output file
    if session_dir:
        result_file = str(session_dir / result_name)
    else:
        result_file = str(output_path.parent / result_name)

    result = {
        "success": final_state.get("typechecks", False),
        "judge_verdict": str(final_state.get("judge_verdict", "PENDING")),
        "synthesis_attempts": final_state.get("attempt", 0),
        "judge_rejections": final_state.get("judge_rejections", {}).get("dafny_synth", 0),
    }

    with open(result_file, 'w') as f:
        json.dump(result, f, indent=2)

    logger.info(f"Result written to: {result_file}")
    return result_file


def main():
    """CLI entry point with proper DBOS initialization."""
    import os
    import sys
    from args import parse_args, merge_session_params
    from config.constants import SESSIONS_DIR
    from tui import run

    args = parse_args()

    # Change to project directory before any relative path resolution
    project_dir = os.path.abspath(args.project)
    if not os.path.isdir(project_dir):
        print(f"Error: --project directory does not exist: {project_dir}")
        sys.exit(1)
    os.chdir(project_dir)

    # Check for resume mode
    resume = getattr(args, 'resume', False)
    session_name = args.session_name

    # Validate --session-name is required
    if not session_name:
        print("Error: --session-name is required")
        sys.exit(1)

    merge_session_params(args)

    # Validate required args (after merge, so resume can provide them)
    if not args.provider:
        print("Error: --provider is required")
        sys.exit(1)
    if not args.model:
        print("Error: --model is required")
        sys.exit(1)
    if not args.input_file:
        print("Error: --input-file is required")
        sys.exit(1)

    input_file = args.input_file
    output_file = args.output_file

    # Create session directory
    session_dir = Path(SESSIONS_DIR) / session_name
    session_dir.mkdir(parents=True, exist_ok=True)
    logger.info(f"Session directory: {session_dir}")

    if not output_file:
        from utils.naming import derive_from_spec, OutputTarget
        output_file = derive_from_spec(input_file, OutputTarget.DAFNY_IMPL)

    # Save session params for potential resume
    from args import save_session_params
    save_session_params(
        session_name=session_name,
        provider=args.provider,
        model=args.model,
        input_file=input_file,
        output_file=output_file,
        max_input_tokens=args.max_input_tokens,
        max_output_tokens=args.max_output_tokens,
        max_total_tokens=args.max_total_tokens,
        max_cost=args.max_cost,
        agent_context=args.agent_context,
    )
    logger.info(f"Session params saved to {session_dir / 'session_params.json'}")

    # Initialize DBOS (skip container to avoid importing all agents)
    DafnySynthAgent._init_dbos_standalone(
        provider=args.provider,
        model=args.model,
        session_name=session_name,
        max_input_tokens=args.max_input_tokens,
        max_output_tokens=args.max_output_tokens,
        max_total_tokens=args.max_total_tokens,
        max_cost=args.max_cost,
        agent_context=args.agent_context,
        skip_container=True,
        resume=resume,
    )

    # Create dependencies BEFORE DBOS.launch()
    from providers import LLMConfig, ReasoningLevel
    from agents.velvet_judge import VelvetJudgeAgent

    config = LLMConfig(provider=args.provider, model=args.model)
    judge = VelvetJudgeAgent(
        config,
        use_tools=False,
        reasoning_level=ReasoningLevel.LOW,
    )
    agent = DafnySynthAgent(config, judge=judge)

    # Now launch DBOS after agent is registered
    DBOS.launch()
    logger.info(f"DBOS launched for standalone {DafnySynthAgent.name}")

    async def workflow():
        from utils.dbos_utils import run_or_resume_workflow
        final_state = await run_or_resume_workflow(
            session_name=session_name,
            resume=resume,
            coro_fn=lambda: run_from_spec(input_file, output_file, agent=agent),
        )
        write_result_json(output_file, final_state, session_dir=session_dir)
        return final_state

    try:
        run(workflow)
    except KeyboardInterrupt:
        sys.exit(130)


if __name__ == "__main__":
    # For standalone execution, use the top-level dafny_synth.py instead
    # Running this file directly causes DBOS class registration issues
    print("Please use: uv run dafny_synth.py [args]")
    print("Running this file directly causes DBOS class registration issues.")
    import sys
    sys.exit(1)
