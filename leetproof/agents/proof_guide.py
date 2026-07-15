from typing import Optional, TYPE_CHECKING
from pathlib import Path

from dbos import DBOS
from langchain_core.messages import HumanMessage

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langgraph.graph import StateGraph, START, END

from agents.spec_state import ExampleProverState
from agents.base import BaseAgent
from logging_config import get_logger
from utils.message_helpers import create_prompt, section, stable

logger = get_logger(__name__)


@DBOS.dbos_class()
class ProofGuideAgent(BaseAgent):
    """Agent that analyzes proofs and provides guidance for completion."""

    name = "proof_guide"
    description = "Analyzes incomplete proofs and provides detailed guidance"

    system_prompt: str = ""

    def __init__(self, config: "LLMConfig", config_name: Optional[str] = None, reasoning_level: "ReasoningLevel | None" = None):
        self._load_system_prompt()
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    def _load_system_prompt(self):
        """Load system prompt from prompts/ProofGuide.md"""
        import os
        base = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))
        prompt_path = base / "prompts" / "ProofGuide.md"
        logger.info(f"Loading proof guide system prompt from {prompt_path}")

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
                f"Loaded proof guide system prompt ({len(self.system_prompt)} chars)"
            )
        else:
            self.system_prompt = "You are a proof guidance system."
            logger.warning(
                f"Prompt file not found at {prompt_path}, using default prompt"
            )

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state)

    def build_graph(self) -> StateGraph:
        """Build the guide graph - simple single node."""
        logger.info("Building ProofGuideAgent graph")

        builder = StateGraph(ExampleProverState)
        builder.add_node("guide", self._guide_node)
        builder.add_edge(START, "guide")
        builder.add_edge("guide", END)

        logger.info("Graph built: START -> guide -> END")
        return builder

    @DBOS.step()
    async def _guide_node(self, state: ExampleProverState) -> dict:
        """
        Analyze the proofs and provide guidance.
        """
        logger.info("Running proof analysis and guidance generation")

        # Construct the guidance prompt
        context_sections = {
            "Specification File": state.get(
                "spec_content", "No specification available"
            ),
            "Current Proofs (incomplete)": state.get(
                "current_proof", "No proofs available"
            ),
            "Build Errors": state.get("build_log", "No build errors available"),
        }

        instructions = """Please analyze the incomplete proofs and provide detailed guidance:

For each test case being proved:
- Summary (what needs to be proved)
- Given/Known (relevant hypotheses and definitions)
- High-level proof strategy
- Step-by-step tactics (exact tactics to run in order)
- Suggested small lemmas (if any)
- Potential pitfalls/fixes
- Checklist & termination criteria
- Confidence & alternatives

Your output should be a structured natural-language document suitable for feeding back into the prover."""

        guidance_prompt = create_prompt(
            task=stable("Analyze the proofs and provide guidance:"),
            sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
            instructions=stable(instructions),
        )

        # Call LLM for guidance
        if self.llm is None:
            raise ValueError("LLM is required for proof guide agent")

        messages = [self.create_system_message(self.system_prompt)]
        self.append_prompt(messages, guidance_prompt)

        logger.debug("Calling LLM for proof guidance")
        response = await self.ainvoke_llm(messages)

        guidance_text = response.content

        # Print the LLM response
        print("\n" + "=" * 80)
        print("PROOF GUIDE LLM RESPONSE:")
        print("=" * 80)
        print(guidance_text)
        print("=" * 80 + "\n")

        logger.info(f"Received guidance ({len(guidance_text)} chars)")

        # Reset attempt counter after providing guidance to give the prover a fresh start
        logger.info(
            "Resetting attempt counter after providing guidance"
        )
        return {"proof_guide_feedback": guidance_text, "attempt": 0}
