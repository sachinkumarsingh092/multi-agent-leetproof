"""
ProofReasoningAgent - Generates informal reasoning and proof sketches for theorems.

This agent takes a goal theorem, file content, and hints, and produces:
1. Informal reasoning: Step-by-step natural language explanation of the proof strategy
2. Proof sketch: A Lean 4 proof skeleton with subgoals marked with sorry

Usage:
    reasoning_agent = ProofReasoningAgent(llm)

    # Get informal reasoning
    reasoning = await reasoning_agent.generate_informal_reasoning(
        goal_theorem="theorem foo : x + 0 = x",
        relevant_context="...",
    )

    # Get proof sketch (uses reasoning + hints)
    sketch = await reasoning_agent.generate_proof_sketch(
        goal_theorem="theorem foo : x + 0 = x",
        file_context="...",  # Pre-filtered context from caller
        informal_reasoning=reasoning,
        hints="...",
    )
"""

from dataclasses import dataclass
from typing import Optional, TYPE_CHECKING

from dbos import DBOS
from langchain_core.messages import HumanMessage, BaseMessage

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langgraph.graph import StateGraph

import json

from agents.base import BaseAgent
from prompts.prompts import (
    INFORMAL_REASONING_SYSTEM,
    LEAN_SKETCH_CREATION_SYSTEM,
    CHECK_MATHEMATICAL_CORRECTNESS_BATCH_SYSTEM,
)
from utils.message_helpers import create_prompt, render_prompt, section, stable, lean_block
from utils.message_constants import AGENT_PROMPT
from logging_config import get_logger

logger = get_logger(__name__)


# ============================================================================
# Output Types
# ============================================================================


@dataclass
class ReasoningResult:
    """Result from informal reasoning generation."""

    informal_reasoning: str
    success: bool = True
    error: Optional[str] = None


@dataclass
class SketchResult:
    """Result from proof sketch generation."""

    sketch: str
    success: bool = True
    error: Optional[str] = None


@dataclass
class GoalCheckInput:
    """Input for goal correctness check."""
    goal_id: str
    goal_statement: str
    context: Optional[str] = None  # Optional per-goal context (appended to shared context)


@dataclass
class CorrectnessResult:
    """Result from mathematical correctness check.

    This matches the JSON schema expected from the LLM:
    {
        "analysis": string,      // Step-by-step reasoning (written FIRST to force thinking)
        "conclusion": string,    // One sentence summary
        "is_provable": boolean,  // Final verdict (written AFTER analysis)
        "justification": string, // Brief explanation
        "correction_hint": string
    }

    The key insight: by requiring 'analysis' and 'conclusion' before 'is_provable',
    we force the LLM to reason through the problem before committing to a boolean.
    This prevents the common issue where the LLM outputs is_provable=false but then
    writes a justification that actually shows it IS provable.
    """

    is_provable: bool
    justification: str
    correction_hint: str = ""
    success: bool = True
    error: Optional[str] = None


# ============================================================================
# ProofReasoningAgent
# ============================================================================


@DBOS.dbos_class()
class ProofReasoningAgent(BaseAgent):
    """
    Agent that generates informal reasoning and proof sketches for theorems.

    This agent bridges the gap between formal theorem statements and
    concrete proof implementations by:
    1. Creating step-by-step natural language reasoning about how to prove a theorem
    2. Generating proof sketches with logical subgoals

    Inherits from BaseAgent to use ainvoke_llm for logging/debugging.
    """

    name = "proof_reasoning"
    description = "Generates informal reasoning and proof sketches for theorem proving"
    system_prompt = ""  # Not used - we have task-specific prompts

    def __init__(self, config: "LLMConfig", config_name: Optional[str] = None, reasoning_level: "ReasoningLevel | None" = None):
        """
        Initialize the proof reasoning agent.

        Args:
            config: LLM configuration (provider + model)
            config_name: Optional DBOS config name
            reasoning_level: Reasoning/thinking level for this agent's LLM calls.
        """
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    def build_graph(self) -> StateGraph:
        """Not used - this agent uses direct method calls instead of graph."""
        raise NotImplementedError(
            "ProofReasoningAgent does not use a graph. "
            "Use generate_informal_reasoning() or generate_proof_sketch() directly."
        )

    async def run_workflow(self, state: dict) -> dict:
        """Not used - this agent uses direct method calls instead of graph."""
        raise NotImplementedError(
            "ProofReasoningAgent does not use run_workflow. "
            "Use generate_informal_reasoning() or generate_proof_sketch() directly."
        )

    def ensure_system_messages(self, messages: list[BaseMessage]) -> None:
        """Override to prevent automatic system message injection.

        ProofReasoningAgent uses task-specific prompts for each method,
        not a single system prompt.
        """
        raise NotImplementedError(
            "ProofReasoningAgent does not use ensure_system_messages. "
            "Each method constructs its own prompt with appropriate system message."
        )

    @DBOS.step()
    async def generate_informal_reasoning(
        self,
        goal_theorem: str,
        relevant_context: str,
        hints: Optional[str] = None,
    ) -> ReasoningResult:
        """
        Generate informal reasoning for how to prove a theorem.

        This produces a step-by-step natural language explanation of the
        proof strategy, useful for both guiding the proof and debugging.

        Args:
            goal_theorem: The theorem statement to prove
            relevant_context: Extracted file context (definitions, specs, helper lemmas)
            hints: Optional hints from RetrieverAgent

        Returns:
            ReasoningResult with the informal reasoning text
        """
        logger.info(f"Generating informal reasoning for: {goal_theorem}...")

        # Build context sections
        context_sections = {
            "Relevant Context": lean_block(relevant_context),
            "Theorem Statement": lean_block(goal_theorem),
        }

        if hints:
            context_sections["Available Hints"] = hints

        prompt = create_prompt(
            task=stable("Give an informal reasoning of the given Lean theorem statement"),
            sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
        )

        messages = [self.create_system_message(INFORMAL_REASONING_SYSTEM)]
        self.append_prompt(messages, prompt)

        try:
            response = await self.ainvoke_llm(messages)
            reasoning = response.content

            logger.info(f"Reasoning:\n{reasoning}")

            return ReasoningResult(
                informal_reasoning=reasoning,
                success=True,
            )

        except Exception as e:
            logger.error(f"Failed to generate informal reasoning: {e}")
            return ReasoningResult(
                informal_reasoning="",
                success=False,
                error=str(e),
            )

    def _build_proof_sketch_system_context(
        self,
        goal_theorem: str,
        file_context: str,
        informal_reasoning: str,
        hints: Optional[str] = None,
    ) -> str:
        """Build static system context for proof sketch generation (cacheable).

        This contains all the context that doesn't change between attempts:
        goal, file context, informal reasoning, and hints.

        Args:
            goal_theorem: The theorem statement to prove
            file_context: Relevant context extracted from the file
            informal_reasoning: Informal reasoning from generate_informal_reasoning()
            hints: Optional hints from RetrieverAgent

        Returns:
            Combined system prompt with LEAN_SKETCH_CREATION_SYSTEM + context
        """
        context_sections = {
            "Goal to Decompose": goal_theorem,
            "File Context": file_context,
            "Informal Reasoning": informal_reasoning,
        }

        if hints:
            context_sections["Useful Hints"] = hints

        static_context = create_prompt(
            task=stable("Create a proof sketch with logical subgoals"),
            sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
        )

        return f"{LEAN_SKETCH_CREATION_SYSTEM}\n\n{render_prompt(static_context).full_text()}"

    @DBOS.step()
    async def generate_proof_sketch(
        self,
        goal_theorem: str,
        file_context: str,
        informal_reasoning: str,
        hints: Optional[str] = None,
        error_feedback: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ) -> SketchResult:
        """
        Generate a proof sketch with logical subgoals.

        This produces a Lean 4 proof skeleton where the main theorem is
        broken down into smaller subgoals using `have` statements.
        Each subgoal is marked with `sorry` for later completion.

        Note: The system context is built from the static parameters (goal, file_context,
        informal_reasoning, hints) and will be cached by the API when identical across calls.

        Args:
            goal_theorem: The theorem statement to prove
            file_context: Relevant context extracted from the file
            informal_reasoning: Informal reasoning from generate_informal_reasoning()
            hints: Optional hints from RetrieverAgent
            error_feedback: Optional error feedback from previous attempt

        Returns:
            SketchResult with the proof sketch and extracted subgoals
        """
        logger.info(f"Generating proof sketch for: {goal_theorem}...")

        # Build system message (static content - cached by API when identical)
        system_content = self._build_proof_sketch_system_context(
            goal_theorem=goal_theorem,
            file_context=file_context,
            informal_reasoning=informal_reasoning,
            hints=hints,
        )

        # Build user message - only contains dynamic error feedback
        if error_feedback:
            user_message = f"""Your previous attempt failed with errors. Please fix and try again.

{error_feedback}

Generate a corrected proof sketch."""
        else:
            user_message = "Please generate the proof sketch for the goal described above."

        messages = [
            self.create_system_message(system_content, message_type=AGENT_PROMPT),
            HumanMessage(content=user_message),
        ]

        try:
            response = await self.ainvoke_llm(messages, reasoning_level=reasoning_level)
            content = response.content

            # Extract the proof sketch from the response
            from utils.lean_helpers import extract_lean_code_from_md_block

            sketch = extract_lean_code_from_md_block(content).strip()

            logger.info(f"Generated proof sketch:\n{sketch}")

            return SketchResult(
                sketch=sketch,
                success=True,
            )

        except Exception as e:
            logger.error(f"Failed to generate proof sketch: {e}")
            return SketchResult(
                sketch="",
                success=False,
                error=str(e),
            )

    async def generate_reasoning_and_sketch(
        self,
        goal_theorem: str,
        file_context: str,
        hints: Optional[str] = None,
    ) -> tuple[ReasoningResult, SketchResult]:
        """
        Convenience method to generate both reasoning and sketch in sequence.

        This is the typical workflow: first generate informal reasoning,
        then use it to create the proof sketch.

        Args:
            goal_theorem: The theorem statement to prove
            file_context: Relevant context extracted from the file
            hints: Optional hints from RetrieverAgent

        Returns:
            Tuple of (ReasoningResult, SketchResult)
        """
        # Step 1: Generate informal reasoning
        reasoning_result = await self.generate_informal_reasoning(
            goal_theorem=goal_theorem,
            relevant_context=file_context,
            hints=hints,
        )

        if not reasoning_result.success:
            return reasoning_result, SketchResult(
                sketch="",
                success=False,
                error="Skipped due to reasoning failure",
            )

        # Step 2: Generate proof sketch using the reasoning
        sketch_result = await self.generate_proof_sketch(
            goal_theorem=goal_theorem,
            file_context=file_context,
            informal_reasoning=reasoning_result.informal_reasoning,
            hints=hints,
        )

        return reasoning_result, sketch_result

    @DBOS.step()
    async def check_goals_correctness_batch(
        self,
        goals: list[GoalCheckInput],
        shared_context: dict[str, str] | str = "",
        reasoning_level: "ReasoningLevel | None" = None,
    ) -> list[CorrectnessResult]:
        """
        Check multiple goals for correctness in a single LLM call.

        Args:
            goals: List of GoalCheckInput objects
            shared_context: Context shared by all goals - either a dict of sections or a string

        Returns:
            List of CorrectnessResult, one per goal in the same order
        """
        if not goals:
            return []

        logger.info(f"Batch checking {len(goals)} goals for correctness")

        # Build goals section with goal_id in context
        goals_text = []
        for goal in goals:
            extra_ctx = f"Goal ID: {goal.goal_id}"
            if goal.context:
                extra_ctx += f"\n{goal.context}"
            goal_section = f"### {goal.goal_id}\n{lean_block(goal.goal_statement)}\n{extra_ctx}"
            goals_text.append(goal_section)

        # Build system message with shared_context (static - cacheable by API)
        if isinstance(shared_context, dict):
            context_parts = [f"## {k}\n{v}" for k, v in shared_context.items()]
            context_str = "\n\n".join(context_parts)
        else:
            context_str = f"## Shared Context\n{shared_context}" if shared_context else ""

        system_content = CHECK_MATHEMATICAL_CORRECTNESS_BATCH_SYSTEM
        if context_str:
            system_content = f"{system_content}\n\n{context_str}"

        # Build user message with just the goals (dynamic per call)
        user_message = f"""Evaluate the following {len(goals)} goals for mathematical correctness and provability.

## Goals to evaluate

{chr(10).join(goals_text)}"""

        messages = [
            self.create_system_message(
                content=system_content,
                message_type=AGENT_PROMPT,
            ),
            HumanMessage(content=user_message),
        ]

        try:
            response = await self.ainvoke_llm(messages, reasoning_level=reasoning_level)
            content = str(response.content).strip()

            # Parse JSON from response
            if "```json" in content:
                content = content.split("```json")[1].split("```")[0].strip()
            elif "```" in content:
                content = content.split("```")[1].split("```")[0].strip()

            start_idx = content.find("{")
            end_idx = content.rfind("}")
            if start_idx != -1 and end_idx != -1:
                content = content[start_idx : end_idx + 1]

            result = json.loads(content)
            results_list = result.get("results", [])

            logger.info(f"Batch correctness check returned {len(results_list)} results")

            # Build result map by goal_id
            result_map = {
                r.get("goal_id", ""): CorrectnessResult(
                    is_provable=r.get("is_provable", True),
                    justification=r.get("justification", ""),
                    correction_hint=r.get("correction_hint", ""),
                    success=True,
                )
                for r in results_list
            }

            # Return results in input order
            return [
                result_map.get(goal.goal_id, CorrectnessResult(
                    is_provable=True,
                    justification="Not in batch response",
                    correction_hint="",
                    success=False,
                ))
                for goal in goals
            ]

        except Exception as e:
            logger.error(f"Failed to batch check goal correctness: {e}")
            return [
                CorrectnessResult(
                    is_provable=True,
                    justification="Batch check failed",
                    correction_hint="",
                    success=False,
                    error=str(e),
                )
                for _ in goals
            ]
