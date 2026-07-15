from typing import Optional, TYPE_CHECKING
from pathlib import Path
import re

from dbos import DBOS
from utils.lean.parser import LeanFile

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from utils.validation_result import ValidationResult
from utils.differ import Differ
from langchain_core.messages import HumanMessage
from langgraph.graph import StateGraph, START, END

from agents.spec_state import ExampleProverState
from agents.base import BaseAgent
from logging_config import get_logger
from utils.message_helpers import create_prompt, section, stable
from tools.common import lean_build_file_helper

logger = get_logger(__name__)


@DBOS.dbos_class()
class ExampleProverAgent(BaseAgent):
    """Agent that proves concrete test cases for specifications."""

    name = "example_prover"
    description = "Formally verifies concrete test cases to validate specifications"

    system_prompt: str = ""
    max_attempts: int = 10

    def __init__(
        self,
        config: "LLMConfig",
        max_attempts: int = 10,
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        self.max_attempts = max_attempts
        self._load_system_prompt()
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    def _load_system_prompt(self):
        """Load system prompt from prompts/ExampleProver.md"""
        import os
        base = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))
        prompt_path = base / "prompts" / "ExampleProver.md"
        logger.info(f"Loading system prompt from {prompt_path}")

        if prompt_path.exists():
            # Read the markdown file and extract content after the frontmatter
            content = prompt_path.read_text()
            # Skip the frontmatter (between --- markers)
            lines = content.split("\n")
            in_frontmatter = False
            prompt_lines = []
            frontmatter_count = 0

            for line in lines:
                if line.strip() == "---":
                    frontmatter_count += 1
                    if frontmatter_count == 2:
                        in_frontmatter = False
                        continue
                    elif frontmatter_count == 1:
                        in_frontmatter = True
                        continue

                if not in_frontmatter and frontmatter_count >= 2:
                    prompt_lines.append(line)

            self.system_prompt = "\n".join(prompt_lines).strip()
            logger.info(
                f"Loaded system prompt ({len(self.system_prompt)} chars) from {prompt_path}"
            )
        else:
            self.system_prompt = (
                "You are a formal verification expert for Lean/Velvet proofs."
            )
            logger.warning(
                f"Prompt file not found at {prompt_path}, using default prompt"
            )

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state)

    def build_graph(self) -> StateGraph:
        """Build the prove -> typecheck loop graph."""
        logger.info("Building ExampleProverAgent graph")

        builder = StateGraph(ExampleProverState)

        builder.add_node("prove", self._prove_node)
        builder.add_node("typecheck", self._typecheck_node)

        builder.add_edge(START, "prove")
        builder.add_edge("prove", "typecheck")
        builder.add_conditional_edges(
            "typecheck", self._should_continue, {"retry": "prove", "done": END}
        )

        logger.info("Graph built: START -> prove -> typecheck -> (retry|done)")
        return builder

    @DBOS.step()
    async def _prove_node(self, state: ExampleProverState) -> dict:
        """Generate or refine proofs using LLM with tools."""

        logger.info(f"Proof attempt {state['attempt'] + 1}/{self.max_attempts}")

        # OPTIMIZATION: Always start fresh - we only need system prompt + current context
        # No need to keep tool call history from previous attempts to save tokens
        messages = []

        if state["attempt"] == 0:
            # First attempt: Add system prompt and initial user message
            logger.info("Mode: Initial proof generation")

            messages.append(self.create_system_message(self.system_prompt))

            # Build context sections
            context_sections = {
                "Verification File (with sorry placeholders)": state["current_proof"]
            }

            # Build instructions
            additional_instructions = f"""
Please complete the formal proofs by replacing all sorry placeholders.

For each test case, prove:
1. Precondition holds
2. Postcondition holds
3. Output uniqueness

The file must typecheck without sorry.

Please provide ONLY the complete Lean code for the verification file in your response.
Do NOT include any explanations, comments, or markdown formatting - just the raw Lean code.
"""

            prompt = create_prompt(
                task=stable("Generate formal verification proofs for test cases:"),
                sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
                instructions=stable(additional_instructions),
                closing=stable("Return ONLY the complete Lean code, no explanations."),
            )

            self.append_prompt(messages, prompt)
        else:
            # Retry: Add new user message with error feedback
            logger.info("Mode: Proof refinement based on errors or ProofGuide feedback")

            messages.append(self.create_system_message(self.system_prompt))

            # Build context sections
            context_sections = {
                "Current Proofs (with errors)": state["current_proof"],
            }

            # Add typecheck errors if available
            if not state.get("typechecks", False) and state.get("build_log"):
                context_sections["Typecheck Errors"] = state["build_log"]

            # Add ProofGuide feedback if available
            if state.get("proof_guide_feedback"):
                context_sections["ProofGuide Feedback"] = state["proof_guide_feedback"]

            # Build additional instructions
            additional_instructions = """
Please fix the issues in the proofs.

Focus on:
- Addressing typecheck errors
- Following ProofGuide's suggestions if provided
- Completing all sorry placeholders

Please provide ONLY the complete Lean code for the verification file in your response.
Do NOT include any explanations, comments, or markdown formatting - just the raw Lean code.
"""

            prompt = create_prompt(
                task=stable("Fix the issues in the proofs:"),
                sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
                instructions=stable(additional_instructions),
                closing=stable("Return ONLY the complete Lean code, no explanations."),
            )

            self.append_prompt(messages, prompt)

        # Call LLM to get proof code
        logger.debug("Calling LLM for proof generation")
        response = await self.ainvoke_llm(messages)

        # Extract proof code from response
        raw_content = str(response.content).strip()

        # Try to extract code from markdown code blocks
        # Look for ```lean, ```lean4, or just ``` blocks
        # This pattern matches: ``` or ```lean or ```lean4 or any other language tag
        code_blocks = re.findall(r"```[a-zA-Z0-9]*\n(.*?)\n```", raw_content, re.DOTALL)

        if code_blocks:
            # If we found code blocks, use the largest one (likely the complete code)
            proof = str(max(code_blocks, key=len)).strip()
            logger.info(
                f"Extracted code from markdown block ({len(code_blocks)} blocks found, using largest)"
            )
        else:
            # No code blocks found, check if the entire content looks like code
            # If it starts with common Lean keywords, assume it's code
            if raw_content.startswith(
                ("import ", "def ", "theorem ", "namespace ", "/-", "--")
            ):
                proof = raw_content
                logger.info("No markdown blocks found, using entire response as code")
            else:
                # LLM didn't follow instructions - log warning and use it anyway
                logger.warning(
                    "Response doesn't appear to be pure Lean code and has no markdown blocks"
                )
                logger.warning(f"First 200 chars: {raw_content[:200]}")
                proof = raw_content

        # Write the proof to the verify file
        if state["verify_file"]:
            verify_path = Path(state["verify_file"])
            verify_path.parent.mkdir(parents=True, exist_ok=True)
            verify_path.write_text(proof)
            logger.info(f"Written proofs to {state['verify_file']}")
        else:
            logger.warning("No verify_file specified, proof not written to disk")

        # OPTIMIZATION: Don't return messages - we don't need the tool call history
        # Next iteration will start fresh with just the proof file content
        return {
            "current_proof": proof,
            "attempt": state["attempt"] + 1,
            # messages are intentionally not included to save tokens
        }

    @DBOS.step()
    def _typecheck_node(self, state: ExampleProverState) -> dict:
        """Run lake env lean to typecheck the proofs."""
        logger.info("Running typecheck with lake build")

        if not state["verify_file"]:
            logger.error("No verify file specified")
            return {"typechecks": False, "build_log": "No verify file specified"}

        # Validate output structure
        validation_result = validate_example_prover_output(
            state["spec_content"], state["current_proof"]
        )
        if validation_result.has_error():
            logger.warning(
                f"ExampleProver output validation failed: {validation_result.get_error()}"
            )
            return {"typechecks": False, "build_log": validation_result.get_error()}
        logger.info("Output validation passed (sections preserved, TestsVerify added)")

        # Use the existing helper instead of reimplementing
        result = lean_build_file_helper(state["verify_file"])

        # Log the result
        if result.typechecks:
            logger.info("✓ Build successful - proofs typecheck correctly")
        else:
            logger.error("❌ BUILD FAILED")
            logger.error(f"File: {state['verify_file']}")
            logger.error(f"Error: {result.build_log}")

        return {"typechecks": result.typechecks, "build_log": result.build_log}

    def _should_continue(self, state: ExampleProverState) -> str:
        """Determine whether to retry or finish."""
        logger.info(
            f"_should_continue: typechecks={state['typechecks']}, attempt={state['attempt']}/{self.max_attempts}"
        )

        if state["typechecks"]:
            logger.info("✓ Proofs typecheck successfully - finishing")
            return "done"
        if state["attempt"] >= self.max_attempts:
            logger.warning(f"✗ Max attempts ({self.max_attempts}) reached - finishing")
            return "done"
        logger.info(f"↻ Retrying... (attempt {state['attempt']}/{self.max_attempts})")
        return "retry"


def validate_example_prover_output(
    old_content: str, new_content: str
) -> ValidationResult:
    """Validate output from ExampleProver agent.

    Required sections: Specs, TestCases, TestsVerify
    Unchanged sections: Specs, TestCases
    """
    required = ["Specs", "TestCases", "TestsVerify"]
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
            f"ExampleProver output missing required sections: {missing}\n"
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
                f"Section '{section_name}' was modified, it should be unchanged. Please address this issue and keep this unchaged.\n"
                f"Diff:\n{d.format()}"
            )

    return ValidationResult.ok()
