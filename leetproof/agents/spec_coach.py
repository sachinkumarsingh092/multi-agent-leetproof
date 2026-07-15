from typing import Optional, TYPE_CHECKING
from pathlib import Path
import re

from dbos import DBOS
from langchain_core.messages import HumanMessage

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langgraph.graph import StateGraph, START, END

from agents.spec_state import SpecAgentState, CoachVerdict
from agents.base import BaseAgent
from logging_config import get_logger
from utils.message_helpers import create_prompt, section, stable
from utils.shutdown import shutdown_boundary

logger = get_logger(__name__)


@DBOS.dbos_class()
class SpecCoachAgent(BaseAgent):
    """Agent that reviews and evaluates generated specifications."""

    name = "spec_coach"
    description = "Reviews specifications and provides feedback on quality"

    system_prompt: str = ""

    def __init__(self, config: "LLMConfig", config_name: Optional[str] = None, reasoning_level: "ReasoningLevel | None" = None):
        self._load_system_prompt()
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    def _load_system_prompt(self):
        """Load system prompt from prompts/SpecCoach.md"""
        import os
        base = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))
        prompt_path = base / "prompts" / "SpecCoach.md"
        logger.info(f"Loading coach system prompt from {prompt_path}")

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
            logger.info(f"Loaded coach system prompt ({len(self.system_prompt)} chars)")
        else:
            self.system_prompt = "You are a specification reviewer."
            logger.warning(
                f"Prompt file not found at {prompt_path}, using default prompt"
            )

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state)

    def build_graph(self) -> StateGraph:
        """Build the coach graph - simple single node."""
        logger.info("Building SpecCoachAgent graph")

        builder = StateGraph(SpecAgentState)
        builder.add_node("review", self._review_node)
        builder.add_edge(START, "review")
        builder.add_edge("review", END)

        logger.info("Graph built: START -> review -> END")
        return builder

    @shutdown_boundary("before spec coach review step")
    @DBOS.step()
    async def _review_node(self, state: SpecAgentState) -> dict:
        """
        Review the specification and provide feedback.

        Returns a verdict: ACCEPT, ACCEPT_WITH_MINOR_ISSUES, or REJECT

        OPTIMIZATION: Coach doesn't need message history - it only reviews
        the current specification file content and provides a verdict.
        """
        logger.info("Running specification review")

        # Construct the evaluation prompt (always fresh, no history needed)
        context_sections = {
            "Problem Description": state["problem_description"],
            "Generated Specification": state["current_spec"],
            "Typecheck Status": f"Typechecks: {state['typechecks']}",
        }

        if not state["typechecks"] and state.get("build_log"):
            context_sections["Build Errors"] = state["build_log"]

        instructions = "Please review this specification according to your evaluation criteria and provide your verdict following the exact output format."

        evaluation_prompt = create_prompt(
            task=stable("Review the following specification:"),
            sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
            instructions=stable(instructions),
        )

        # Call LLM for review
        if self.llm is None:
            raise ValueError("LLM is required for coach agent")

        messages = [self.create_system_message(self.system_prompt)]
        self.append_prompt(messages, evaluation_prompt)

        logger.info("Calling LLM for specification review")
        response = await self.ainvoke_llm(messages)

        # Ensure response content is a string
        review_text = response.content
        if not isinstance(review_text, str):
            review_text = str(review_text)

        # Print the LLM response
        logger.info("\n" + "=" * 80)
        logger.info("COACH LLM RESPONSE:")
        logger.info("=" * 80)
        logger.info(review_text)
        logger.info("=" * 80 + "\n")

        logger.info(f"Received review ({len(review_text)} chars)")

        # Parse the verdict and score from the response
        verdict = self._parse_verdict(review_text)
        score = self._parse_score(review_text)

        logger.info(f"Parsed verdict: {verdict.value}, score: {score}/40")

        result = {
            "coach_verdict": verdict,
            "coach_feedback": review_text,
            "coach_score": score,
        }

        # OPTIMIZATION: Coach never needs to return messages
        # The feedback text itself contains all the information needed
        # for the next iteration. No conversation history is required.
        logger.info(f"Coach verdict: {verdict.value} (score: {score}/40)")

        return result

    def _parse_verdict(self, review_text: str) -> CoachVerdict:
        """
        Parse the verdict from the coach's response.

        Expected format: ### Verdict\n{Accept / Accept with Minor Issues / Reject}
        """
        # Look for verdict section
        lines = review_text.strip().split("\n")

        for i, line in enumerate(lines):
            # Look for "### Verdict" or "Verdict" heading
            if "verdict" in line.lower() and line.strip().startswith("#"):
                # Check next non-empty line
                for j in range(i + 1, len(lines)):
                    verdict_line = lines[j].strip()
                    if verdict_line:
                        verdict_lower = verdict_line.lower()
                        if (
                            "accept with" in verdict_lower
                            or "minor issues" in verdict_lower
                        ):
                            logger.info("Verdict parsed as ACCEPT_WITH_MINOR_ISSUES")
                            return CoachVerdict.ACCEPT_WITH_MINOR_ISSUES
                        elif "accept" in verdict_lower:
                            logger.info("Verdict parsed as ACCEPT")
                            return CoachVerdict.ACCEPT
                        elif "reject" in verdict_lower:
                            logger.info("Verdict parsed as REJECT")
                            return CoachVerdict.REJECT
                        break

        # If we can't parse it, default to REJECT for safety
        logger.warning(f"Could not parse verdict from response, defaulting to REJECT")
        return CoachVerdict.REJECT

    def _parse_score(self, review_text: str) -> int:
        """
        Parse the total score from the coach's response.

        Expected format: **Total Score:** {score}/40
        """
        # Look for "Total Score:" pattern
        score_pattern = r"\*\*Total Score:\*\*\s*(\d+)\s*/\s*40"
        match = re.search(score_pattern, review_text)

        if match:
            score = int(match.group(1))
            logger.info(f"Parsed score: {score}/40")
            return score

        # If we can't find it, try alternative patterns
        alt_pattern = r"Total[:\s]+(\d+)\s*/\s*40"
        match = re.search(alt_pattern, review_text, re.IGNORECASE)

        if match:
            score = int(match.group(1))
            logger.info(f"Parsed score (alt): {score}/40")
            return score

        # Default to 0 if we can't parse
        logger.warning("Could not parse score from response, defaulting to 0")
        return 0
