"""Lean Synthesis and Verification Agent.

This agent combines:
1. Lean synthesis (generating pure Lean functional implementations from specifications)
2. Proof generation (proving the implementation satisfies the specification)

The flow is:
1. Parse specs to extract precondition/postcondition definitions
2. Generate the implementation using LLM
3. Construct a correctness theorem:
   theorem correctness_goal (params) (h_precond : precondition params)
       : postcondition params (implementation params) := by
       sorry
4. Create a Proof section with the theorem
5. Dispatch to the prover agent to prove it
"""

from typing import Optional, List, TYPE_CHECKING
from dataclasses import dataclass
import re

from dbos import DBOS

if TYPE_CHECKING:
    from utils.lean_proof_parser import LeanTheorem
    from providers import LLMConfig, ReasoningLevel
from pathlib import Path

from langchain_core.messages import HumanMessage, SystemMessage
from langgraph.graph import StateGraph, START, END
from providers import ReasoningLevel

from agents.agent_state import VelvetAgentState, RetryLimitExceeded, JudgeVerdict, GoalStatus, GoalState, PBTStatus
from config.limits import Limits
from agents.velvet_judge import VelvetJudgeAgent
from agents.base import BaseAgent
from agents.velvet_proof_orchestrator import GoalProver
from utils.shutdown import shutdown_boundary, shutdown_hook, ShutdownHookMode
from tools.common import (
    lean_build_file_helper,
    write_method,
    lean_diagnostics_messages,
)
from tools.mcp_tools import get_lean_lsp_tools
from tools.lean_explore_tool import lean_explore_search
from utils.lean.parser import LeanFile, Section, parse_test_cases
from utils.lean.types import Param
from utils.lean_proof_parser import parse_lean_theorem
from utils.lean_helpers import (
    get_def_by_name,
    parse_def_params,
    generate_lean_assertions,
    construct_correctness_goal,
    build_lean_impl_pbt_section,
)
from utils.velvet_types import VelvetMethod, NameInfo
from utils.velvet_helpers import (
    SET_MAX_HEARTBEATS,
    get_pbt_counterexamples,
    format_pbt_feedback,
    run_two_phase_pbt,
)
from utils.validation import validate_output_file
from utils.validation_result import ValidationResult
from utils.differ import Differ
from utils.program_state import ProgramBuffer
from logging_config import get_logger
from utils.message_helpers import create_prompt, dynamic, section, stable
from config.limits import Limits
from utils.proof_types import ProvingContext
from utils.analytics.lean_synth_and_verify import (
    AttemptMeta,
    AttemptOutcome,
    JudgeResult,
    ProofStatus,
    ProofSummary,
    TypecheckSummary,
    write_attempt_meta,
    write_judge_result,
    write_proof_summary,
    write_typecheck_summary,
)
from utils.lean.build import find_project_root
from utils.lean.constants import (
    LEAN_SYNTH_IMPORTS,
    PANTOGRAPH_CORE_OPTIONS,
    PANTOGRAPH_OPTIONS,
    SET_LOOM_CHOICE_DEMONIC,
    SET_LOOM_TERMINATION_PARTIAL,
    SET_LOOM_TERMINATION_TOTAL,
)
from tools.pantograph_client import PantographClient, PantographFactory

logger = get_logger(__name__)

LEAN_SYNTH_PROVER_V2_MAX_ITERATIONS = 35
LEAN_SYNTH_PROVER_V2_MAX_LEAN_EXPLORE_CALLS = 8
LEAN_SYNTH_PROVER_V2_CONFIG_NAME = "ProverV2AgentLeanSynth"


# --- Prompt Constants ---

LEAN_LSP_TOOLS = """**Lean LSP Tools Available:**
- `lean_diagnostics_messages`: Get pretty-printed LSP diagnostics filtered by severity (error/warning/info/all, default error)
  Use this to debug type errors and other compilation issues."""

WRITE_METHOD_RULES = """- Use the `write_method` tool to write ONLY your function implementation
- Your function MUST be named `implementation` - always use this exact name
- The tool will automatically place it in the Impl section (other sections are preserved)
- Output ONLY the def (signature + body), NOT imports or other sections
- TIP: For array access syntax, prefer `arr[i]!`, `arr[i]'(by ...)`, or `arr[i]?` instead of deprecated forms like `Array.get!` / `Array.get`
- Do NOT call write_method multiple times
- After writing, immediately respond with ONLY the text 'Done' and make NO MORE TOOL CALLS"""


# --- Validation ---

def find_implementation_def(impl_content: str) -> "Optional[LeanTheorem]":
    """Find the 'implementation' function from Impl section content.

    Parses all declarations and returns the one named 'implementation'.
    Returns None if not found.
    """
    from utils.lean_proof_parser import extract_declarations, LeanDef

    decls = extract_declarations(impl_content)
    for decl in decls:
        if decl.name == "implementation" and isinstance(decl, LeanDef):
            # Parse it fully to get params/return type
            try:
                return parse_lean_theorem(decl.content)
            except Exception:
                return None
    return None


def validate_impl_signature(old_impl: str, new_impl: str) -> Optional[str]:
    """Validate that 'implementation' function signature is unchanged.

    Finds the function named 'implementation' in both old and new content,
    then compares their signatures.

    Returns None if valid, error message if invalid.
    If the original has no 'implementation' function (e.g., first run), skips validation.
    """
    old_parsed = find_implementation_def(old_impl)
    new_parsed = find_implementation_def(new_impl)

    if not old_parsed:
        # No implementation in original - skip signature validation (first run or dummy)
        return None
    if not new_parsed:
        return "Could not find 'implementation' function in new Impl section"

    # Check params count
    if len(old_parsed.params) != len(new_parsed.params):
        return f"Parameter count changed: expected {len(old_parsed.params)}, got {len(new_parsed.params)}"

    # Check each param
    for i, (old_p, new_p) in enumerate(zip(old_parsed.params, new_parsed.params)):
        if old_p.names != new_p.names:
            return f"Parameter {i} names changed: expected {old_p.names}, got {new_p.names}"
        if old_p.type_expr != new_p.type_expr:
            return f"Parameter {i} type changed: expected '{old_p.type_expr}', got '{new_p.type_expr}'"
        if old_p.kind != new_p.kind:
            return f"Parameter {i} kind changed: expected {old_p.kind}, got {new_p.kind}"

    # Check return type
    if old_parsed.return_type != new_parsed.return_type:
        return f"Return type changed: expected '{old_parsed.return_type}', got '{new_parsed.return_type}'"

    return None


def validate_lean_synth_output(old_content: str, new_content: str) -> ValidationResult:
    """Validate output from Lean Synthesizer."""
    required = ["Specs", "Impl"]
    unchanged = ["Specs"]

    try:
        old_file = LeanFile.from_content(old_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse old content: {e}")

    try:
        new_file = LeanFile.from_content(new_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse new content: {e}")

    # Check required sections exist
    missing = [s for s in required if not new_file.has_section(s)]
    if missing:
        return ValidationResult.error(f"Missing sections: {missing}")

    # Check unchanged sections
    for section_name in unchanged:
        d = Differ(
            f"old:{section_name}",
            old_file.get_section(section_name, assert_exists=True).content.strip(),
            f"new:{section_name}",
            new_file.get_section(section_name, assert_exists=True).content.strip(),
        )
        if not d.is_empty():
            return ValidationResult.error(f"Section '{section_name}' was modified")

    # Check Impl signature unchanged
    old_impl = old_file.get_section("Impl")
    new_impl = new_file.get_section("Impl")

    if old_impl and new_impl:
        sig_error = validate_impl_signature(old_impl.content, new_impl.content)
        if sig_error:
            return ValidationResult.error(f"Implementation signature modified: {sig_error}")

    return ValidationResult.ok()


@dataclass(frozen=True)
class SpecSignatureParts:
    """Parsed signature information derived from the Specs section."""

    precond_params: list[Param]
    postcond_params: list[Param]
    result_params: list[Param]
    has_precondition: bool


def extract_spec_signature_parts(specs_content: str) -> SpecSignatureParts:
    """Extract precondition/postcondition/result parameters from a Specs section."""
    precond_def = get_def_by_name(specs_content, "precondition")
    postcond_def = get_def_by_name(specs_content, "postcondition")
    if not postcond_def:
        raise ValueError("Specs section missing 'postcondition' definition")

    precond_params = parse_def_params(precond_def.content) if precond_def else []
    postcond_params = parse_def_params(postcond_def.content)
    precond_param_names = {p.name for p in precond_params}
    result_params = [p for p in postcond_params if p.name not in precond_param_names]
    if not result_params:
        raise ValueError("postcondition missing result parameter(s)")

    return SpecSignatureParts(
        precond_params=precond_params,
        postcond_params=postcond_params,
        result_params=result_params,
        has_precondition=precond_def is not None,
    )


_SORRY_OR_ADMIT_RE = re.compile(r"\b(sorry|admit)\b")


def has_sorry_or_admit(program_text: str) -> bool:
    """Check for sorry/admit after stripping comments from Lean text."""
    from utils.lean.parser import _remove_comments

    return bool(_SORRY_OR_ADMIT_RE.search(_remove_comments(program_text)))


# --- Agent ---

@DBOS.dbos_class()
class LeanSynthAndVerifyAgent(BaseAgent):
    """Agent that synthesizes Lean implementations and proves them correct."""

    name = "lean_synth_and_verify"
    description = "Synthesizes Lean implementations and proves them correct"

    system_prompt: str = ""
    max_attempts: int = Limits.VELVET_PROGRAMMER_MAX_ATTEMPTS
    max_judge_rejections: int = 20

    def __init__(
        self,
        config: "LLMConfig",
        *,
        judge: "VelvetJudgeAgent",
        prover: GoalProver,
        max_attempts: int = Limits.VELVET_PROGRAMMER_MAX_ATTEMPTS,
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self.max_attempts = max_attempts
        self.judge = judge
        self.prover = prover

        from utils.prompt_helpers import load_system_prompt
        self.system_prompt = load_system_prompt(
            "lean_synthesizer.md",
            "You are a Lean programming expert. Generate correct pure Lean functional code from specifications.",
        )

        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    async def get_tools(self) -> list:
        return [write_method, lean_diagnostics_messages, lean_explore_search]

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state, {"recursion_limit": 100})

    def build_graph(self) -> StateGraph:
        """Build the synthesis -> proof graph."""
        builder = StateGraph(VelvetAgentState)

        # Synthesis nodes
        builder.add_node("generate", self._generate_node)
        builder.add_node("repair_and_typecheck", self._repair_and_typecheck_node)
        builder.add_node("judge", self._judge_node)
        builder.add_node("setup_retry_after_judge", self._setup_retry_after_judge_node)

        # Proof nodes
        builder.add_node("prepare_proof", self._prepare_proof_node)
        builder.add_node("prove_goal", self._prove_goal_node)
        builder.add_node("assemble_final", self._assemble_final_node)

        # Synthesis flow
        builder.add_edge(START, "generate")
        builder.add_edge("generate", "repair_and_typecheck")
        builder.add_conditional_edges(
            "repair_and_typecheck",
            self._should_continue_after_typecheck,
            {"retry": "generate", "judge": "judge"},
        )
        builder.add_conditional_edges(
            "judge",
            self._should_continue_after_judge,
            {"retry": "setup_retry_after_judge", "prove": "prepare_proof"},
        )
        builder.add_edge("setup_retry_after_judge", "generate")

        # Proof flow
        builder.add_edge("prepare_proof", "prove_goal")
        builder.add_edge("prove_goal", "assemble_final")
        builder.add_edge("assemble_final", END)

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

    def _current_attempt_reasoning_level(self, state: VelvetAgentState) -> "ReasoningLevel":
        """Return the reasoning level used for the current attempt."""
        return self._select_reasoning_level(max(0, state["attempt"] - 1))

    def _write_attempt_meta(
        self,
        state: VelvetAgentState,
        *,
        outcome: AttemptOutcome,
        error_message: str | None = None,
    ) -> None:
        """Write attempt-level analytics metadata for the current attempt."""
        write_attempt_meta(
            self._analytics_attempt(state),
            AttemptMeta(
                final_outcome=outcome,
                reasoning_level=self._current_attempt_reasoning_level(state).value,
                error_message=error_message,
                file_path=state["output_file"],
            ),
        )

    def _record_typecheck_analytics(
        self,
        state: VelvetAgentState,
        *,
        validation_passed: bool,
        build_passed: bool,
        pbt_failure: bool,
        pbt_status: PBTStatus | None,
        build_log: str,
        pbt_failure_message: str | None = None,
    ) -> None:
        """Store the lean synth typecheck/build summary for one attempt."""
        program_text = ProgramBuffer.from_dict(state["program_state"]).get_current()
        impl_text = LeanFile.from_content(program_text).get_section(
            "Impl", assert_exists=True
        ).full_text()
        attempt_log = self._analytics_attempt(state)

        write_typecheck_summary(
            attempt_log,
            TypecheckSummary(
                validation_passed=validation_passed,
                build_passed=build_passed,
                pbt_failure=pbt_failure,
                program=program_text,
                impl_section=impl_text,
                pbt_status=pbt_status,
                pbt_failure_message=pbt_failure_message,
            ),
            text=build_log,
        )

        if not (validation_passed and build_passed and not pbt_failure):
            final_outcome = (
                AttemptOutcome.VALIDATION_FAILURE
                if not validation_passed
                else AttemptOutcome.PBT_FAILURE
                if pbt_failure
                else AttemptOutcome.BUILD_FAILURE
            )
            self._write_attempt_meta(
                state,
                outcome=final_outcome,
                error_message=pbt_failure_message or build_log,
            )

    def _record_judge_analytics(
        self,
        state: VelvetAgentState,
        *,
        verdict: JudgeVerdict,
        reasoning: str,
    ) -> None:
        """Store the judged Lean implementation, verdict, and reasoning."""
        attempt_log = self._analytics_attempt(state)
        write_judge_result(
            attempt_log,
            JudgeResult(
                verdict=verdict,
                reasoning=reasoning,
                program=ProgramBuffer.from_dict(state["program_state"]).get_current(),
            ),
        )
        if verdict == JudgeVerdict.FAIL:
            self._write_attempt_meta(
                state,
                outcome=AttemptOutcome.JUDGE_FAIL,
                error_message=reasoning,
            )

    def _record_proof_analytics(
        self,
        state: VelvetAgentState,
        *,
        proof_status: ProofStatus,
        final_build_passed: bool,
        build_log: str,
        error_message: str | None = None,
    ) -> None:
        """Store proof/final-assembly analytics for one lean synth attempt."""
        final_program = ProgramBuffer.from_dict(state["program_state"]).get_stable() or ""
        has_sorry = has_sorry_or_admit(final_program)

        final_outcome = {
            ProofStatus.PREPARATION_FAILED: AttemptOutcome.PROOF_PREPARATION_FAILURE,
            ProofStatus.PROVEN: AttemptOutcome.PROOF_PROVEN,
            ProofStatus.PARTIAL: AttemptOutcome.PROOF_PARTIAL,
            ProofStatus.FAILED: AttemptOutcome.PROOF_FAILED,
        }[proof_status]
        if proof_status != ProofStatus.PREPARATION_FAILED and not final_build_passed:
            final_outcome = AttemptOutcome.FINAL_BUILD_FAILURE
            error_message = error_message or build_log or "Final assembly build failed"

        attempt_log = self._analytics_attempt(state)
        write_proof_summary(
            attempt_log,
            ProofSummary(
                status=proof_status,
                has_sorry=has_sorry,
                final_build_passed=final_build_passed,
                program=final_program,
                error_message=error_message,
            ),
            text=build_log,
        )
        self._write_attempt_meta(
            state,
            outcome=final_outcome,
            error_message=error_message,
        )

    def _mark_attempt_terminal(
        self,
        state: VelvetAgentState,
        *,
        outcome: AttemptOutcome,
        error_message: str,
    ) -> None:
        """Write terminal attempt metadata for workflow-level exhaustion/failure."""
        self._write_attempt_meta(state, outcome=outcome, error_message=error_message)

    def _clean_specs_content(self, specs_content: str) -> str:
        """Remove register_specdef_allow_recursion from specs content.

        Args:
            specs_content: The original specs section content

        Returns:
            Cleaned specs content without register_specdef_allow_recursion
        """
        lines = specs_content.split('\n')
        cleaned_lines = [
            line for line in lines
            if 'register_specdef_allow_recursion' not in line
        ]
        return '\n'.join(cleaned_lines)

    def _filter_prologue_content(self, prologue: str) -> str:
        """Filter prologue content to exclude imports and specific options.

        Removes:
        - All import statements
        - the standard Loom semantics options handled elsewhere

        Args:
            prologue: The original prologue content

        Returns:
            Filtered prologue content (non-import, non-excluded-option content)
        """
        lines = prologue.split('\n')
        filtered_lines = []

        excluded_options = {
            SET_LOOM_TERMINATION_PARTIAL,
            SET_LOOM_TERMINATION_TOTAL,
            SET_LOOM_CHOICE_DEMONIC,
        }

        for line in lines:
            line_stripped = line.strip()
            # Skip all imports
            if line_stripped.startswith('import '):
                continue
            # Skip excluded options
            if line_stripped in excluded_options:
                continue
            filtered_lines.append(line)

        return '\n'.join(filtered_lines)

    def _prepare_output_file(self, state: VelvetAgentState) -> LeanFile:
        """Prepare the output file with proper sections.

        Constructs a new Lean file with:
        - Filtered prologue content from input spec (excluding specific imports/options)
        - Standard imports (Lean, Mathlib.Tactic, Velvet.Std, Extensions.VelvetPBT)
        - SET_MAX_HEARTBEATS
        - Specs section (from specification)
        - Impl section (with dummy implementation)
        - TestCases section (from specification)
        - Assertions section (generated from test cases)
        - Pbt section (initially empty; populated deterministically after typecheck)

        Returns the LeanFile object.
        """
        output_path = Path(state["output_file"])
        output_path.parent.mkdir(parents=True, exist_ok=True)

        # Parse input specification to extract sections
        input_file = LeanFile.from_content(state["specification"])

        specs_section = input_file.get_section("Specs")
        testcases_section = input_file.get_section("TestCases")

        if not specs_section:
            raise ValueError("Input file missing required 'Specs' section")
        if not testcases_section:
            raise ValueError("Input file missing required 'TestCases' section")

        # Parse precondition/postcondition for implementation signature
        signature = extract_spec_signature_parts(specs_section.content)
        impl_params = signature.precond_params
        result_params = signature.result_params

        # Create prologue with only imports and settings
        prologue = """import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

""" + SET_MAX_HEARTBEATS + "\n"

        # Get filtered prologue content (non-import content from original spec)
        filtered_prologue = self._filter_prologue_content(input_file.prologue)

        # Create sections list
        sections = []

        # 1. Specs section with filtered prologue content prepended
        cleaned_specs_content = self._clean_specs_content(specs_section.content)

        # Prepend filtered prologue content to Specs section
        if filtered_prologue.strip():
            # Add filtered prologue content before the specs content
            specs_content_with_prologue = filtered_prologue.rstrip() + "\n\n" + cleaned_specs_content
        else:
            specs_content_with_prologue = cleaned_specs_content

        sections.append(Section(name="Specs", content=specs_content_with_prologue))

        # 2. Impl section with dummy implementation
        params_str = " ".join(f"({p.name} : {p.ty})" for p in impl_params)
        # Everything apart from the preconidtion params are tupled and put in as a output param
        output_ty = " × ".join([param.ty for param in result_params])
        dummy_impl = f"def implementation {params_str} : {output_ty} :=\n  sorry"
        sections.append(Section(name="Impl", content=dummy_impl))
        logger.info("Created dummy Impl section with sorry")

        # 3. TestCases section
        sections.append(Section(name="TestCases", content=testcases_section.content))

        # 4. Assertions section (generated from test cases)
        func_name = "implementation"
        params_tuples = [(p.name, p.ty) for p in impl_params]

        mock_method = VelvetMethod(
            name=func_name,
            params=[NameInfo(name=p.name, ty=p.ty, is_mut=False) for p in impl_params],
            returns=NameInfo(name="result", ty=output_ty, is_mut=False),
            requires=[],
            ensures=[],
        )
        test_cases = parse_test_cases(testcases_section.content, mock_method)

        if test_cases:
            assertions_content = generate_lean_assertions(func_name, params_tuples, test_cases)
            sections.append(Section(name="Assertions", content=assertions_content))
            logger.info(f"Generated Assertions section with {len(test_cases)} test cases")

        # 5. Pbt section (filled after typecheck if plausible testing can be enabled)
        sections.append(Section(name="Pbt", content=""))

        # Construct LeanFile and write
        lean_file = LeanFile(prologue=prologue, sections=sections)
        lean_file.reconstruct_and_write_to_file(output_path)
        return lean_file

    @shutdown_boundary("before lean synth generate step")
    @DBOS.step()
    async def _generate_node(self, state: VelvetAgentState) -> dict:
        """Generate or refine the Lean function using LLM with tools."""
        attempt = state["attempt"] + 1
        logger.info(f"Synthesis attempt {attempt}/{self.max_attempts}")

        output_path = Path(state["output_file"])

        # First time: prepare the output file with all sections
        if not output_path.exists():
            logger.info(f"Preparing output file: {output_path}")
            self._prepare_output_file(state)

        # Store prepared content for signature validation (needed on first attempt)
        prepared_content = None
        buffer = ProgramBuffer.from_dict(state["program_state"])
        if buffer.get_stable() is None:
            prepared_content = output_path.read_text()

        # Read current state of file
        lean_file = LeanFile.from_path(state["output_file"])
        specs_section = lean_file.get_section("Specs", assert_exists=True)
        testcases_section = lean_file.get_section("TestCases", assert_exists=True)

        # Build context - fresh each time, no message history
        # Extract prologue content from original specification
        input_file = LeanFile.from_content(state["specification"])
        filtered_prologue = self._filter_prologue_content(input_file.prologue)

        stable_context_sections = {
            "Specification": specs_section.content,
            "TestCases": testcases_section.content,
        }

        # Add prologue content if it exists
        if filtered_prologue.strip():
            stable_context_sections["Additional Definitions and Context"] = filtered_prologue

        dynamic_context_sections = {}

        # Include context from judge rejection (old impl)
        if state.get("judge_context"):
            dynamic_context_sections.update(state["judge_context"])

        if state["attempt"] > 0:
            # Retry after typecheck failure: include current impl and errors
            buffer = ProgramBuffer.from_dict(state["program_state"])
            current_lean_file = LeanFile.from_content(buffer.get_current())
            current_impl = current_lean_file.get_section("Impl", assert_exists=True).content
            dynamic_context_sections["Current Implementation (with errors)"] = current_impl
            dynamic_context_sections["Build Errors"] = state["build_log"]

        if state.get("judge_reasoning"):
            dynamic_context_sections["Judge Feedback"] = state["judge_reasoning"]

        task_desc = "Generate a pure Lean functional implementation for the following specification:"

        retry_note = None
        if state.get("judge_reasoning"):
            retry_note = "Your previous implementation was rejected. Please address the feedback above or try a different approach."
        elif state["attempt"] > 0:
            retry_note = "Your previous implementation had errors. Please fix them."

        prompt_sections = tuple(
            section(k, stable(v)) for k, v in stable_context_sections.items()
        ) + tuple(
            section(k, dynamic(v)) for k, v in dynamic_context_sections.items()
        ) + (
            (section("Issues To Address", dynamic(retry_note)),)
            if retry_note
            else ()
        )
        prompt = create_prompt(
            task=stable(task_desc),
            sections=prompt_sections,
            instructions=stable(
                f"{LEAN_LSP_TOOLS}\n\nOutput file: {state['output_file']}\n\n{WRITE_METHOD_RULES}"
            ),
            closing=stable("Focus on correctness. The code must typecheck."),
        )

        # Fresh messages each time
        messages = []
        self.ensure_system_messages(messages)
        self.append_prompt(messages, prompt)

        response = await self.invoke_with_tools(
            messages,
            max_iterations=Limits.LEAN_SYNTH_MAX_ITERATIONS,
            reasoning_level=self._select_reasoning_level(state["attempt"]),
        )

        if state["output_file"] and Path(state["output_file"]).exists():
            program = Path(state["output_file"]).read_text()
        else:
            program = response.content

        buffer = ProgramBuffer.from_dict(state["program_state"])
        update = {
            "program_state": buffer.update_current(program),
            "attempt": state["attempt"] + 1,
        }
        if prepared_content:
            update["program_state"] = buffer.update_stable(prepared_content)
        return update

    def _try_add_pbt(self, output_file: str):
        """Try to add a Velvet PBT wrapper around the pure Lean implementation."""
        logger.info("Attempting to add PBT section for Lean implementation")
        lean_file = LeanFile.from_path(output_file)
        specs_section = lean_file.get_section("Specs", assert_exists=True)

        signature = extract_spec_signature_parts(specs_section.content)
        precond_params = signature.precond_params
        result_params = signature.result_params
        has_precondition = signature.has_precondition

        return run_two_phase_pbt(
            output_file,
            lambda max_ms: build_lean_impl_pbt_section(
                precond_params,
                result_params,
                has_precondition=has_precondition,
                max_ms=max_ms,
            ),
            compile_failure_comment="Lean wrapper for velvet_plausible_test failed to compile. Giving up on PBT.",
            log_prefix="Lean PBT",
        )

    @DBOS.step()
    def _repair_and_typecheck_node(self, state: VelvetAgentState) -> dict:
        """Typecheck the program and run Velvet-style PBT via a wrapper method."""
        logger.info("Running typecheck")

        is_valid, error_state = validate_output_file(state)
        if not is_valid:
            return error_state

        buffer = ProgramBuffer.from_dict(state["program_state"])
        existing_pbt_status = state.get("pbt_status", PBTStatus.NOT_ATTEMPTED)

        # Validate against stable content (prepared content with dummy impl) for signature checking
        stable_content = buffer.get_stable()
        if not stable_content:
            return {"typechecks": False, "build_log": "No stable content for validation"}
        validation_result = validate_lean_synth_output(
            stable_content,
            buffer.get_current(),
        )
        if validation_result.has_error():
            build_log = validation_result.get_error()
            self._record_typecheck_analytics(
                state,
                validation_passed=False,
                build_passed=False,
                pbt_failure=False,
                pbt_status=existing_pbt_status,
                build_log=build_log,
            )
            return {"typechecks": False, "build_log": build_log, "pbt_status": existing_pbt_status}

        result = lean_build_file_helper(state["output_file"], include_info_logs=True)
        counterexamples = get_pbt_counterexamples(result.diagnostics)
        if counterexamples:
            feedback = format_pbt_feedback(counterexamples)
            logger.warning(f"Lean PBT found {len(counterexamples)} counterexamples")
            self._record_typecheck_analytics(
                state,
                validation_passed=True,
                build_passed=result.typechecks,
                pbt_failure=True,
                pbt_status=existing_pbt_status,
                build_log=feedback,
                pbt_failure_message="\n".join(d.message for d in counterexamples),
            )
            return {
                "typechecks": False,
                "build_log": feedback,
                "pbt_status": existing_pbt_status,
            }

        if not result.typechecks:
            build_log = result.as_string(["error"])
            self._record_typecheck_analytics(
                state,
                validation_passed=True,
                build_passed=False,
                pbt_failure=False,
                pbt_status=existing_pbt_status,
                build_log=build_log,
            )
            return {
                "typechecks": False,
                "build_log": build_log,
                "pbt_status": existing_pbt_status,
            }

        pbt_status = existing_pbt_status
        analytics_build_passed = True
        analytics_pbt_failure = False
        analytics_build_log = result.as_string(["info", "warning"])
        analytics_pbt_failure_message = None

        if pbt_status == PBTStatus.NOT_ATTEMPTED:
            pbt_status, pbt_build_result, pbt_result = self._try_add_pbt(state["output_file"])
            if pbt_result:
                analytics_build_passed = pbt_build_result.typechecks if pbt_build_result is not None else True
                analytics_pbt_failure = True
                analytics_build_log = pbt_result["build_log"]
                analytics_pbt_failure_message = pbt_result["build_log"]
                self._record_typecheck_analytics(
                    state,
                    validation_passed=True,
                    build_passed=analytics_build_passed,
                    pbt_failure=analytics_pbt_failure,
                    pbt_status=pbt_status,
                    build_log=analytics_build_log,
                    pbt_failure_message=analytics_pbt_failure_message,
                )
                return {**pbt_result, "pbt_status": pbt_status}
            if pbt_build_result is not None:
                analytics_build_passed = pbt_build_result.typechecks
                analytics_build_log = pbt_build_result.as_string(["info", "warning"] if pbt_build_result.typechecks else ["error"])

        program = Path(state["output_file"]).read_text()
        self._record_typecheck_analytics(
            state,
            validation_passed=True,
            build_passed=analytics_build_passed,
            pbt_failure=analytics_pbt_failure,
            pbt_status=pbt_status,
            build_log=analytics_build_log,
            pbt_failure_message=analytics_pbt_failure_message,
        )
        return {
            "typechecks": True,
            "build_log": analytics_build_log,
            "pbt_status": pbt_status,
            "program_state": buffer.update_current(
                program,
                promote_to_stable=True,
            ),
            **self._save_phase_result(state, program),
        }

    # NOTE: Step-in-step with judge.evaluate — see velvet_programmer._judge_node
    # for full rationale. Safe because post-evaluate code is trivial dict
    # construction, and removing the step would expose the file read to stale
    # disk state on replay.
    @shutdown_boundary("before lean synth judge step")
    @DBOS.step()
    async def _judge_node(self, state: VelvetAgentState) -> dict:
        """Evaluate the output using judge with caching optimization."""
        logger.info("Running judge evaluation")

        lean_file = LeanFile.from_path(state["output_file"])
        impl_section = lean_file.get_section("Impl", assert_exists=True)

        # Dynamic context: changes per evaluation
        dynamic_ctx = {
            "Build Status": f"Build Passed: {state['typechecks']}",
            "Build Log": "No Build Errors Detected" if state["typechecks"] else state["build_log"],
            "Specification": state["specification"],
            "Output produced by the Agent": impl_section.content,
        }

        verdict, reasoning = await self.judge.evaluate(
            agent_name=self.name,
            agent_system_prompt=self.system_prompt,
            dynamic_ctx=dynamic_ctx,
            static_ctx=None,  # lean_synth doesn't have additional docs
        )

        result = {
            "judge_verdict": verdict,
            "judge_reasoning": reasoning,
        }
        self._record_judge_analytics(state, verdict=verdict, reasoning=reasoning)

        # Track rejections
        if verdict == JudgeVerdict.FAIL:
            rejections_dict = dict(state.get("judge_rejections", {}))
            current = rejections_dict.get(self.name, 0)
            rejections_dict[self.name] = current + 1
            result["judge_rejections"] = rejections_dict
            logger.info(f"Judge rejected {self.name} (rejection #{rejections_dict[self.name]})")

        return result

    @DBOS.step()
    def _setup_retry_after_judge_node(self, state: VelvetAgentState) -> dict:
        """Set up state for retry after judge rejection."""
        logger.info("Setting up retry after judge rejection")

        lean_file = LeanFile.from_path(state["output_file"])
        impl_section = lean_file.get_section("Impl", assert_exists=True)

        # Store rejected impl in judge_context for next attempt
        judge_context = dict(state.get("judge_context", {}))
        judge_context["Previous Implementation (rejected by judge)"] = impl_section.content

        return {
            "judge_context": judge_context,
        }

    @shutdown_boundary("before lean synth prepare-proof step")
    @DBOS.step()
    async def _prepare_proof_node(self, state: VelvetAgentState) -> dict:
        """Prepare the proof by constructing the correctness theorem."""
        logger.info("=== Preparing Proof ===")

        file_path = state["output_file"]
        lean_file = LeanFile.from_path(file_path)
        specs_section = lean_file.get_section("Specs", assert_exists=True)

        try:
            signature = extract_spec_signature_parts(specs_section.content)
        except ValueError as e:
            logger.error(str(e))
            return {"goals": [], "build_log": str(e)}

        # Construct the correctness goal
        goal = construct_correctness_goal(
            impl_name="implementation",
            precond_params=signature.precond_params,
            postcond_params=signature.postcond_params,
            has_precondition=signature.has_precondition,
        )

        logger.info(f"Constructed correctness goal:\n{goal.as_sorried()}")

        # Add Proof section at the end with sorry to verify theorem typechecks
        lean_file.add_or_replace_section("Proof", goal.as_sorried())
        lean_file.reconstruct_and_write_to_file(Path(file_path))

        result = lean_build_file_helper(file_path)
        if not result.typechecks:
            logger.error(f"Proof section failed to typecheck: {result.as_string(['error'])}")
            program = Path(file_path).read_text()
            buffer = ProgramBuffer.from_dict(state["program_state"])
            return {
                "goals": [],
                "build_log": result.as_string(["error"]),
                "program_state": buffer.update_current(
                    program,
                    promote_to_stable=True,
                ),
            }

        # Clear Proof section so prover agent can work on it
        lean_file.add_or_replace_section("Proof", "")
        final_content = lean_file.reconstruct_and_write_to_file(Path(file_path))
        logger.info("Cleared Proof section for prover agent")

        goal_state: GoalState = {
            "goal": goal.to_dict(),  # Serialize for DBOS persistence
            "status": GoalStatus.UNPROCESSED,
            "description": "",
            "failures": [],
            "proof_result": None
        }

        buffer = ProgramBuffer.from_dict(state["program_state"])
        return {
            "goals": [goal_state],
            "program_state": buffer.update_current(
                final_content,
                promote_to_stable=True,
            ),
            "build_log": ""
        }

    # NOTE: No @DBOS.step() — this node calls prove_goal (a child @DBOS.workflow),
    # and DBOS forbids starting a workflow from within a step. The file write at
    # the end (Path.write_text) is necessary because prove_goal's _finalize_result
    # is a @DBOS.step() whose file-write side effect is skipped on replay — the
    # explicit write here ensures the file matches result.content regardless of
    # whether prove_goal ran fresh or replayed cached steps.
    async def _prove_goal_node(self, state: VelvetAgentState) -> dict:
        """Prove the correctness goal using the prover agent."""
        from utils.shutdown import handle_shutdown_if_requested
        handle_shutdown_if_requested("before proving goal")

        file_path = state["output_file"]
        goals = state.get("goals", [])

        if not goals:
            logger.warning("No goals to prove")
            return {}

        from utils.lean.types import Goal

        goal_state = goals[0]
        goal_dict = goal_state["goal"]
        goal = Goal.from_dict(goal_dict) if isinstance(goal_dict, dict) else goal_dict

        logger.info(f"Proving correctness goal: {goal.name}")
        logger.info(f"GOAL:\n{goal.as_sorried()}")

        from utils.proof_types import (
            PantographParams,
            AttemptBudgetConfigBundle,
            AttemptBudgetConfig,
            AttemptBudgetMode,
        )
        project_path = find_project_root(file_path)
        from utils.lean.constants import AUTOMATION
        from utils.context_utils import SpecsImplProofSignaturesExtractor
        attempt_budgets = AttemptBudgetConfigBundle(
            shallow=AttemptBudgetConfig(
                mode=AttemptBudgetMode.UP,
                base=10,
                slope=2,
                min_attempts=10,
                max_attempts=15,
            ),
            decomposition=AttemptBudgetConfig(
                mode=AttemptBudgetMode.DOWN,
                base=10,
                slope=2,
                min_attempts=10,
                max_attempts=10,
            ),
        )

        ctx = ProvingContext(
            file_path=file_path,
            goal=goal,
            sections=["Specs", "Impl", "Proof"],
            pantograph=PantographParams(
                key=goal.name,
                project_path=project_path,
                imports=LEAN_SYNTH_IMPORTS,
                options=PANTOGRAPH_OPTIONS,
                core_options=PANTOGRAPH_CORE_OPTIONS,
            ),
            automation_tactics=AUTOMATION,
            informal_reasoning="",
            context_extractor=SpecsImplProofSignaturesExtractor(),
            attempt_budgets=attempt_budgets,
            hint_sections=["Specs"],
        )

        try:
            with shutdown_hook(
                ShutdownHookMode.CLEAR_AND_PUSH,
                lambda: self.prover.write_shutdown_snapshot(ctx),
            ):
                result = await self.prover.prove(
                    ctx=ctx,
                    max_depth=Limits.PROOF_GUIDE_MAX_DEPTH,
                )
        finally:
            PantographFactory.cleanup(ctx.pantograph.key)

        final_goal = result.filtered_goal if result.filtered_goal else goal
        Path(file_path).write_text(result.content)

        if result.success:
            status = GoalStatus.PARTIAL if result.has_sorry else GoalStatus.PROVEN
            description = f"Partial ({len(result.failures)} sorries)" if result.has_sorry else "Proven"
        else:
            status = GoalStatus.FAILED
            description = f"Failed: {result.error[:200]}"

        # Serialize Goal and ProofResult for DBOS persistence
        updated_goals = [{
            **goal_state,
            "status": status,
            "description": description,
            "failures": result.failures,
            "proof_result": result.to_dict() if hasattr(result, 'to_dict') else None,
            "goal": final_goal.to_dict() if hasattr(final_goal, 'to_dict') else final_goal,
        }]

        buffer = ProgramBuffer.from_dict(state["program_state"])
        return {
            "goals": updated_goals,
            "program_state": buffer.update_current(
                result.content,
                promote_to_stable=True,
            ),
        }

    @shutdown_boundary("before lean synth assemble-final step")
    @DBOS.step()
    async def _assemble_final_node(self, state: VelvetAgentState) -> dict:
        """Final assembly and typecheck."""
        from utils.lean.parser import _remove_comments

        file_path = state["output_file"]
        buffer = ProgramBuffer.from_dict(state["program_state"])
        final_program = buffer.get_stable() or ""

        logger.info("=== Final Assembly ===")

        sorry_count = _remove_comments(final_program).count("sorry")
        logger.info(f"Final proof contains {sorry_count} sorries")

        typecheck_result = lean_build_file_helper(file_path)

        if typecheck_result.typechecks:
            logger.info(f"Final proof typechecks ({sorry_count} sorries)")
        else:
            logger.error("Final proof failed to typecheck")

        phase_results = state.get("phase_results", {}).copy()
        phase_results[self.name] = {
            "stable_content": final_program,
            "build_log": typecheck_result.build_log,
            "typechecks": typecheck_result.typechecks
        }

        goals = state.get("goals", [])
        if not goals:
            proof_status = ProofStatus.PREPARATION_FAILED
            error_message = state.get("build_log") or "Proof preparation failed"
        else:
            goal_status = goals[0].get("status")
            if goal_status == GoalStatus.PROVEN:
                proof_status = ProofStatus.PROVEN
                error_message = None
            elif goal_status == GoalStatus.PARTIAL:
                proof_status = ProofStatus.PARTIAL
                error_message = None
            else:
                proof_status = ProofStatus.FAILED
                error_message = goals[0].get("description") or typecheck_result.build_log or "Proof failed"

        analytics_state = {
            **state,
            "program_state": buffer.update_current(final_program, promote_to_stable=True),
        }
        self._record_proof_analytics(
            analytics_state,
            proof_status=proof_status,
            final_build_passed=typecheck_result.typechecks,
            build_log=typecheck_result.build_log,
            error_message=error_message,
        )

        return {
            "program_state": buffer.update_current(
                final_program,
                promote_to_stable=True,
            ),
            "build_log": typecheck_result.build_log,
            "typechecks": typecheck_result.typechecks,
            "phase_results": phase_results,
        }

    def _should_continue_after_typecheck(self, state: VelvetAgentState) -> str:
        if state.get("typechecks"):
            return "judge"
        if state["attempt"] >= self.max_attempts:
            self._mark_attempt_terminal(
                state,
                outcome=AttemptOutcome.SYNTHESIS_EXHAUSTED,
                error_message=state.get("build_log", "Failed to synthesize a valid program"),
            )
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=self.max_attempts,
                reason="Failed to generate typechecking code",
            )
        return "retry"

    def _should_continue_after_judge(self, state: VelvetAgentState) -> str:
        if state.get("judge_verdict") == JudgeVerdict.PASS:
            return "prove"

        rejections = state.get("judge_rejections", {}).get(self.name, 0)
        if rejections >= self.max_judge_rejections:
            self._mark_attempt_terminal(
                state,
                outcome=AttemptOutcome.JUDGE_RETRY_LIMIT_EXCEEDED,
                error_message=state.get("judge_reasoning", "Judge rejected too many times"),
            )
            raise RetryLimitExceeded(
                agent_name=self.name,
                attempts=rejections,
                reason="Judge rejected too many times",
            )
        return "retry"


async def run_from_spec(
    input_file: str,
    output_file: str,
    agent: "LeanSynthAndVerifyAgent",
) -> dict:
    """Run synthesis and verification from a spec file.

    Requires DBOS to be initialized first (via main()).

    Args:
        input_file: Path to the spec file
        output_file: Path to write the implementation
        agent: Initialized standalone synthesis agent.
    """
    from tools.common import set_allowed_output_files

    spec = Path(input_file).read_text()
    set_allowed_output_files([output_file])

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

    return await agent.run_workflow(state)


def write_result_json(output_file: str, final_state: dict, session_dir: Optional[Path] = None) -> str:
    """Write result stats to JSON file.

    Args:
        output_file: Path to the output .lean file
        final_state: Final workflow state
        session_dir: Optional session directory to write result to
    """
    import json

    # Derive result filename from output file
    output_path = Path(output_file)
    if output_file.endswith(".lean"):
        result_name = output_path.stem + "_result.json"
    else:
        result_name = output_path.name + "_result.json"

    # Put in session directory if provided, otherwise next to output file
    if session_dir:
        result_file = str(session_dir / result_name)
    else:
        result_file = str(output_path.parent / result_name)

    goals = final_state.get("goals", [])
    goals_proven = sum(1 for g in goals if g.get("status") == GoalStatus.PROVEN)
    goals_partial = sum(1 for g in goals if g.get("status") == GoalStatus.PARTIAL)
    goals_failed = sum(1 for g in goals if g.get("status") == GoalStatus.FAILED)

    # Check for sorry/admit in final program (ignoring comments)
    final_program = ProgramBuffer.from_dict(
        final_state["program_state"]
    ).get_stable() or ""
    has_sorry = has_sorry_or_admit(final_program)

    result = {
        "typechecks": final_state.get("typechecks", False),
        "goals_total": len(goals),
        "goals_proven": goals_proven,
        "goals_partial": goals_partial,
        "goals_failed": goals_failed,
        "has_sorry": has_sorry,
        "judge_verdict": str(final_state.get("judge_verdict", "PENDING")),
        "synthesis_attempts": final_state.get("attempt", 0),
    }

    with open(result_file, 'w') as f:
        json.dump(result, f, indent=2)

    logger.info(f"Result written to: {result_file}")
    return result_file


def main():
    """CLI entry point with proper DBOS initialization."""
    import os
    import sys
    from runner import run
    from agents.base import BaseAgent
    from args import parse_args, merge_session_params
    from config.constants import SESSIONS_DIR

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

    # Create session directory if session_name provided
    session_dir = None
    if session_name:
        session_dir = Path(SESSIONS_DIR) / session_name
        session_dir.mkdir(parents=True, exist_ok=True)
        logger.info(f"Session directory: {session_dir}")

    if not output_file:
        from utils.naming import derive_from_spec, OutputTarget
        output_file = derive_from_spec(input_file, OutputTarget.LEAN_IMPL)

    # Save session params for potential resume
    if session_dir:
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

    # Initialize DBOS (skip container to avoid double-import issues)
    # This does NOT call DBOS.launch() when skip_container=True
    LeanSynthAndVerifyAgent._init_dbos_standalone(
        provider=args.provider,
        model=args.model,
        session_name=args.session_name,
        max_input_tokens=args.max_input_tokens,
        max_output_tokens=args.max_output_tokens,
        max_total_tokens=args.max_total_tokens,
        max_cost=args.max_cost,
        agent_context=args.agent_context,
        skip_container=True,
        resume=resume,
    )

    # Create all dependencies BEFORE DBOS.launch()
    from providers import LLMConfig, ReasoningLevel
    from agents.retriever_agent import RetrieverAgent
    from agents.proof_reasoning_agent import ProofReasoningAgent
    from agents.prover_agent import ProverAgent
    from agents.prover_v2_agent import ProverV2Agent

    config = LLMConfig(provider=args.provider, model=args.model)
    judge = VelvetJudgeAgent(
        config,
        use_tools=False,
        reasoning_level=ReasoningLevel.LOW,
    )
    reasoning = ProofReasoningAgent(config, reasoning_level=ReasoningLevel.MEDIUM)
    retriever = RetrieverAgent(config)
    prover = ProverAgent(config, retriever=retriever, reasoning=reasoning)
    prover_v2 = ProverV2Agent(
        config,
        prover=prover,
        retriever=retriever,
        reasoning=reasoning,
        default_max_iterations=LEAN_SYNTH_PROVER_V2_MAX_ITERATIONS,
        max_lean_explore_calls=LEAN_SYNTH_PROVER_V2_MAX_LEAN_EXPLORE_CALLS,
        config_name=LEAN_SYNTH_PROVER_V2_CONFIG_NAME,
        reasoning_level=ReasoningLevel.MEDIUM,
    )
    agent = LeanSynthAndVerifyAgent(config, judge=judge, prover=prover_v2)

    # Now launch DBOS after agent is registered
    from dbos import DBOS
    DBOS.launch()
    logger.info(f"DBOS launched for standalone {LeanSynthAndVerifyAgent.name}")

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
    print("Please use: lloom-agent lean-synth [args]")
    print("Running this file directly causes DBOS class registration issues.")
    import sys
    sys.exit(1)
