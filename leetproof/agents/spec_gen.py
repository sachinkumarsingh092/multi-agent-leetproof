from typing import Optional, TYPE_CHECKING
from pathlib import Path

from dbos import DBOS
from utils.lean.parser import LeanFile
from utils.validation_result import ValidationResult
from langchain_core.messages import HumanMessage

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langgraph.graph import StateGraph, START, END

from agents.spec_state import CoachVerdict, SpecAgentState
from agents.base import BaseAgent
from tools.spec_gen_tools import get_spec_gen_tools
from logging_config import get_logger, log_with_truncation
from utils.message_helpers import create_prompt, code_block, lean_block
from utils.spec_rag import get_rag_instance
from utils.shutdown import shutdown_boundary
from config.limits import Limits
from utils.lean.constants import (
    SET_LOOM_CHOICE_DEMONIC,
    SET_LOOM_TERMINATION_TOTAL,
    SET_MAX_HEARTBEATS,
    SET_PP_COERCIONS,
)
import logging

logger = get_logger(__name__)


@DBOS.dbos_class()
class SpecGenAgent(BaseAgent):
    """Agent that generates Velvet specifications from natural language descriptions.

    This agent's responsibility is to generate ONE specification per invocation.
    It does NOT iterate - iteration is handled by the main workflow which calls
    SpecGen -> typecheck -> Coach -> SpecGen (if needed).
    """

    name = "spec_gen"
    description = "Generates formal Velvet specifications from natural language problem descriptions"

    system_prompt: str = ""
    velvet_reference: str = ""  # Velvet syntax reference for user prompt
    max_attempts: int = Limits.SPEC_GEN_MAX_ATTEMPTS

    def __init__(self, config: "LLMConfig", config_name: Optional[str] = None, reasoning_level: "ReasoningLevel | None" = None):
        self._load_system_prompt()
        self._load_velvet_reference()
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)

    async def get_tools(self) -> list:
        """Get SpecGen-specific tools.

        SpecGen has minimal, focused tools:
        - write_file: Write the specification to the configured output file
        """
        return await get_spec_gen_tools()

    @DBOS.workflow()
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow."""
        return await self.graph.ainvoke(state)

    def _log_llm_prompt(self, messages: list, phase: str = "LLM Call"):
        """Log the complete prompt being sent to LLM."""
        logger.info("")
        logger.info("-" * 80)
        logger.info(f"📝 {phase}: Complete Prompt")
        logger.info("-" * 80)

        for i, msg in enumerate(messages, 1):
            msg_type = type(msg).__name__.replace("Message", "")
            logger.info(f"\n[Message {i}] Type: {msg_type}")
            logger.info("-" * 40)

            content = msg.content if hasattr(msg, "content") else str(msg)

            # Log with truncation for console, full for file
            # Console shows first 1500 chars, file gets everything
            log_with_truncation(logger, logging.INFO, content, console_max_length=1500)

        logger.info("")
        logger.info("-" * 80)
        logger.info(f"Total messages: {len(messages)}")
        total_chars = sum(
            len(m.content if hasattr(m, "content") else str(m)) for m in messages
        )
        logger.info(f"Total prompt length: {total_chars} characters")
        logger.info("-" * 80)
        logger.info("")

    def _load_system_prompt(self):
        """Load and split content from prompts/SpecGen.md"""
        import os
        base = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))
        prompt_path = base / "prompts" / "SpecGen.md"
        logger.info(f"Loading content from {prompt_path}")

        # Simple, stable system prompt for caching
        self.system_prompt = "You are a software-specification engineer working with Velvet — a hybrid verification language that combines SMT solving with Lean proofs."

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

            # Store the document content for use in human messages
            self.document_content = "\n".join(prompt_lines).strip()
            logger.info(
                f"Loaded document content from {prompt_path}"
            )
        else:
            self.document_content = ""
            logger.warning(
                f"Prompt file not found at {prompt_path}, using default prompts"
            )

    def _load_velvet_reference(self):
        """Load Velvet language reference for user prompt."""
        self.velvet_reference = """
## Velvet Language Quick Reference

**Data Types**: `Int`, `Nat` (non-negative), `Array <T>`, `List <T>`, `Bool`, `Char`, `Unit`

**Array Operations**: `arr.size`, `arr[i]!` (access), `arr.toList`

**Logical Operators**: `∧` (and), `∨` (or), `→` (implies), `↔` (iff), `¬` (not), `∀` (forall), `∃` (exists)

**Method Signature**:
```lean
method FuncName (param: Type) return (result: Type)
  require precondition
  ensures postcondition
  do
  pure <value>  -- placeholder
```

**Helper Functions** (use Lean syntax):
```lean
def helperName (x: Type) : ReturnType :=
  -- definition
```

**Polymorphic Methods** (explicit type parameters):
```lean
method reverse (α : Type) (l: List α) return (res: List α)
```

**Checklist**: Use `Nat` for non-negative values • Include necessary preconditions • Use `!` for array access • Ensure postconditions determine output uniquely
"""
        logger.info(f"Loaded Velvet reference ({len(self.velvet_reference)} chars)")

    @staticmethod
    def _select_reasoning_level(attempt_index: int, max_attempts: int) -> "ReasoningLevel":
        """Escalate spec generation reasoning across retry thirds."""
        from providers import ReasoningLevel

        two_thirds = max(1, (2 * max_attempts) // 3)

        if attempt_index < two_thirds:
            return ReasoningLevel.LOW
        return ReasoningLevel.MEDIUM

    def _current_attempt_reasoning_level(self, state: SpecAgentState) -> "ReasoningLevel":
        """Return the reasoning level for the in-flight generation attempt."""
        attempt_index = max(0, int(state.get("specgen_attempt", 0)))
        max_attempts = max(1, int(state.get("specgen_max_attempt", self.max_attempts)))
        return self._select_reasoning_level(attempt_index, max_attempts)

    def build_graph(self) -> StateGraph:
        """Build a graph with planning and generation nodes.

        Flow:
        - START -> plan (only on first attempt) -> generate -> END
        - On retry attempts, skip planning and go directly to generate
        """
        logger.info("Building SpecGenAgent graph")

        builder = StateGraph(SpecAgentState)

        # Add nodes
        builder.add_node("plan", self._plan_node)
        builder.add_node("generate", self._generate_node)

        # Conditional start: plan on first attempt, skip on retries
        def should_plan(state: SpecAgentState) -> str:
            """Decide whether to run planning phase."""
            if state.get("specgen_attempt", 0) == 0:
                logger.info("First attempt: will run planning phase")
                return "plan"
            else:
                logger.info(
                    f"Retry attempt {state['specgen_attempt']}: skipping planning"
                )
                return "generate"

        builder.add_conditional_edges(
            START, should_plan, {"plan": "plan", "generate": "generate"}
        )

        # After planning, go to generate
        builder.add_edge("plan", "generate")

        # After generate, we're done
        builder.add_edge("generate", END)

        logger.info("Graph built: START -> [plan] -> generate -> END")
        return builder

    @shutdown_boundary("before specgen planning step")
    @DBOS.step()
    async def _plan_node(self, state: SpecAgentState) -> dict:
        """Planning phase: LLM identifies key concepts, then search for relevant Lean declarations.

        Workflow:
        1. Ask LLM to identify 3 key concepts needed for the problem
        2. Parse LLM response to extract concept names
        3. Search Mathlib for each concept separately
        4. Combine planning thoughts + search results
        """
        logger.info("")
        logger.info("=" * 80)
        logger.info("RETRIEVAL STEP 1: Planning Phase - LLM-guided Concept Search")
        logger.info("=" * 80)
        logger.info(f"Problem: {state['problem_id']}")
        logger.info(f"Problem description: {state['problem_description'][:100]}...")
        logger.info("")

        # Use LeanExplore via spec_rag.py instead of MCP tools
        try:
            from utils.spec_rag import SpecRAG
            import os
            import re

            # Check if LeanExplore is disabled via environment variable
            disable_lean = os.getenv("DISABLE_LEAN_EXPLORE", "").lower() in (
                "1",
                "true",
                "yes",
            )

            if disable_lean:
                logger.warning(
                    "LeanExplore disabled via DISABLE_LEAN_EXPLORE environment variable"
                )
                logger.warning("Skipping planning phase")
                return {"planning_results": ""}

            logger.info("Initializing RAG system with LeanExplore integration...")
            rag = SpecRAG()

            # Step 1: Ask LLM to identify key concepts
            logger.info("")
            logger.info("Step 1: Asking LLM to identify at least 3 key concepts...")
            logger.info("-" * 40)

            planning_prompt = f"""Analyze the following programming problem and identify at least 3 key mathematical concepts or data structures that would be needed to write a formal specification.

Problem:
{state["problem_description"]}

Think about:
- What data structures are needed? (e.g., List, Array, Set)
- What mathematical properties need to be verified? (e.g., sorted, prime, divisible)
- What operations are central to the problem? (e.g., maximum, reverse, filter)

Respond in EXACTLY this format (one concept per line):
CONCEPT 1: <concept name or search term>
CONCEPT 2: <concept name or search term>
CONCEPT 3: <concept name or search term>

Example response:
CONCEPT 1: A list is sorted
CONCEPT 2: Reverse a list
CONCEPT 3: The maximum number in a list of Nat

Now provide your concepts:"""

            planning_messages = [
                self.create_system_message(
                    "You are a helpful assistant that identifies key mathematical concepts for formal verification."
                ),
                HumanMessage(content=planning_prompt),
            ]

            # Log the planning prompt
            self._log_llm_prompt(
                planning_messages,
                phase="Planning Phase - Step 1: Concept Identification",
            )

            # Call LLM to get concepts (without tools)
            logger.info("Calling LLM to identify concepts...")
            llm_response = await self.ainvoke_llm(
                planning_messages,
                reasoning_level=self._current_attempt_reasoning_level(state),
            )

            # Extract content and ensure it's a string
            if hasattr(llm_response, "content"):
                if isinstance(llm_response.content, list):
                    # If content is a list, join it into a string
                    planning_thoughts = "\n".join(
                        str(item) for item in llm_response.content
                    )
                else:
                    planning_thoughts = str(llm_response.content)
            else:
                planning_thoughts = str(llm_response)

            logger.info("LLM Planning Response:")
            logger.info("-" * 40)
            logger.info(planning_thoughts)
            logger.info("-" * 40)
            logger.info("")

            # Step 2: Parse concepts from LLM response
            logger.info("Step 2: Parsing concepts from LLM response...")
            logger.info("-" * 40)

            # Extract concepts using regex
            concept_pattern = r"CONCEPT\s+\d+:\s*(.+)"
            concept_matches = re.findall(
                concept_pattern, planning_thoughts, re.IGNORECASE
            )

            # Clean up concepts (strip whitespace)
            concepts = [c.strip() for c in concept_matches]

            if concepts:
                logger.info(f"✓ Extracted {len(concepts)} concepts:")
                for i, concept in enumerate(concepts, 1):
                    logger.info(f"  [{i}] {concept}")
            else:
                logger.warning(
                    "No concepts extracted, will use full problem description"
                )
            logger.info("")

            # Step 3: Search Mathlib for each concept
            logger.info("Step 3: Searching Mathlib for each concept...")
            logger.info("-" * 40)

            all_lean_results = []
            search_details = []

            if concepts:
                # Search for each concept separately
                for i, concept in enumerate(concepts, 1):
                    logger.info(f"Searching for concept {i}: '{concept}'...")
                    concept_results = await rag.search_lean(
                        query=concept,
                        top_k=3,  # Get top 3 results per concept
                    )

                    if concept_results:
                        logger.info(
                            f"  ✓ Found {len(concept_results)} declarations for '{concept}'"
                        )
                        for result in concept_results:
                            logger.info(f"    - {result.get('lean_name', 'N/A')}")
                        all_lean_results.extend(concept_results)
                        search_details.append(
                            f"**Concept {i}: {concept}** → Found {len(concept_results)} declarations"
                        )
                    else:
                        logger.info(f"  ⚠ No declarations found for '{concept}'")
                        search_details.append(
                            f"**Concept {i}: {concept}** → No declarations found"
                        )
                    logger.info("")
            else:
                # Fallback: search with full problem description
                logger.info("Fallback: Searching with full problem description...")
                all_lean_results = await rag.search_lean(
                    query=state["problem_description"], top_k=5
                )
                search_details.append(
                    f"**Full problem search** → Found {len(all_lean_results)} declarations"
                )

            # Step 4: LLM Review - Filter useful definitions
            logger.info("Step 4: LLM Review - Filtering useful definitions...")
            logger.info("-" * 40)

            if all_lean_results:
                # Prepare review prompt with all found definitions
                definitions_for_review = rag.format_lean_results_for_prompt(
                    all_lean_results
                )

                review_prompt = f"""Review the following Lean/Mathlib definitions that were found for this problem:

Problem:
{state["problem_description"]}

Identified Concepts:
{planning_thoughts}

Found Definitions:
{definitions_for_review}

Task: Review all the definitions above and select ONLY the ones that are directly useful for writing a formal specification for this problem.

For each useful definition, explain briefly (1 sentence) why it's relevant.

Respond in this format:
USEFUL DEFINITION 1: <lean_name> - <definition> - <path> - <reason>
USEFUL DEFINITION 2: <lean_name> - <definition> - <path> - <reason>
...

If a definition is not directly useful, do NOT include it.
Be selective - only choose definitions that will actually be used in the specification."""

                review_messages = [
                    self.create_system_message(
                        "You are a helpful assistant that reviews Lean/Mathlib definitions for formal verification tasks."
                    ),
                    HumanMessage(content=review_prompt),
                ]

                # Log the review prompt
                self._log_llm_prompt(
                    review_messages, phase="Planning Phase - Step 4: LLM Review"
                )

                # Call LLM to review definitions
                logger.info("Calling LLM to review and filter definitions...")
                review_response = await self.ainvoke_llm(
                    review_messages,
                    reasoning_level=self._current_attempt_reasoning_level(state),
                )

                # Extract content
                if hasattr(review_response, "content"):
                    if isinstance(review_response.content, list):
                        review_text = "\n".join(
                            str(item) for item in review_response.content
                        )
                    else:
                        review_text = str(review_response.content)
                else:
                    review_text = str(review_response)

                logger.info("LLM Review Response:")
                logger.info("-" * 40)
                logger.info(review_text)
                logger.info("-" * 40)
                logger.info("")

                # Parse selected definitions from review
                import re

                useful_pattern = r"USEFUL DEFINITION \d+:\s*([^\s-]+)"
                selected_names = re.findall(useful_pattern, review_text, re.IGNORECASE)

                logger.info(f"✓ LLM selected {len(selected_names)} useful definitions:")
                for i, name in enumerate(selected_names, 1):
                    logger.info(f"  [{i}] {name}")
                logger.info("")

                # Filter all_lean_results to only include selected definitions
                if selected_names:
                    filtered_results = []
                    for result in all_lean_results:
                        lean_name = result.get("lean_name", "")
                        # Check if this definition was selected (match by name)
                        if any(
                            sel_name in lean_name or lean_name in sel_name
                            for sel_name in selected_names
                        ):
                            filtered_results.append(result)

                    logger.info(
                        f"✓ Filtered from {len(all_lean_results)} to {len(filtered_results)} definitions"
                    )
                else:
                    logger.warning(
                        "No definitions selected by LLM, using all found definitions as fallback"
                    )
                    filtered_results = all_lean_results
            else:
                review_text = "No definitions to review."
                filtered_results = []

            # Step 5: Format final planning results
            logger.info("Step 5: Formatting final planning results...")
            logger.info("-" * 40)

            planning_results = ""

            # Add LLM's planning thoughts
            planning_results += "# Planning Analysis\n\n"
            planning_results += (
                "The LLM identified the following key concepts for this problem:\n\n"
            )
            planning_results += planning_thoughts + "\n\n"
            planning_results += "---\n\n"

            # Add LLM's review and selection
            if all_lean_results:
                planning_results += "# LLM Review\n\n"
                planning_results += f"The LLM found {len(filtered_results)} useful ones:\n\n"
                planning_results += review_text + "\n\n"
                planning_results += "---\n\n"

            # Add detailed Lean declarations (only filtered/selected ones)
            if filtered_results:
                planning_results += "# Selected Lean Definitions\n\n"
                planning_results += (
                    "The following definitions were selected as directly useful:\n\n"
                )
                planning_results += rag.format_lean_results_for_prompt(filtered_results)
            else:
                planning_results += "No useful Lean definitions found.\n"

            logger.info(f"Planning Results Summary:")
            logger.info(f"  - Total declarations found: {len(all_lean_results)}")
            logger.info(f"  - Selected by LLM: {len(filtered_results)}")
            if filtered_results:
                logger.info(f"  Selected declarations:")
                for i, result in enumerate(filtered_results, 1):
                    logger.info(f"    [{i}] {result.get('lean_name', 'N/A')}")
            logger.info(
                f"  - Total formatted output: {len(planning_results)} characters"
            )
            logger.info("")

        except FileNotFoundError as e:
            logger.warning(f"LeanExplore data not available: {e}")
            logger.warning("Continuing without Lean declarations")
            planning_results = ""
        except Exception as e:
            logger.warning(f"Failed to search LeanExplore: {e}")
            logger.warning("Continuing without Lean declarations")
            planning_results = ""

        # Add RAG phase to planning
        logger.info("")
        logger.info("=" * 80)
        logger.info("RETRIEVAL STEP 2: RAG Phase - Retrieving Similar Specifications")
        logger.info("=" * 80)
        logger.info(f"Query: {state['problem_description'][:100]}...")
        logger.info("Search method: Hybrid BM25 + Embedding search")
        logger.info("Retrieving top 3 similar specifications...")
        logger.info("")

        try:
            from utils.spec_rag import get_rag_instance
            rag_instance = get_rag_instance()
            similar_specs = rag_instance.retrieve(
                query=state["problem_description"],
                top_k=3,  # Retrieve top 3 similar specs
            )
            rag_examples = rag_instance.format_examples_for_prompt(similar_specs)

            logger.info(f"RAG Results Summary:")
            logger.info(
                f"  - Retrieved {len(similar_specs)} similar specification(s)"
            )

            # Log details of each retrieved example
            for i, spec in enumerate(similar_specs, 1):
                logger.info(f"  [{i}] ID: {spec.get('problem_id', 'unknown')}")
                # Show score if available
                if "score" in spec or "_score" in spec:
                    score = spec.get("score", spec.get("_score", "N/A"))
                    logger.info(f"      Similarity score: {score}")
                # Show problem description preview
                prob_desc = spec.get(
                    "problem_description", spec.get("description", "")
                )
                if prob_desc:
                    preview = prob_desc[:80].replace("\n", " ")
                    logger.info(f"      Description: {preview}...")

            logger.info(
                f"  - Total formatted examples: {len(rag_examples)} characters"
            )
            logger.info("")

            # Add RAG results to planning results
            if rag_examples:
                planning_results += "\n\n---\n\n"
                planning_results += "# Similar Specification Examples\n\n"
                planning_results += rag_examples

        except Exception as e:
            logger.warning(
                f"RAG retrieval failed: {e}, continuing without examples"
            )
            logger.info("")

        logger.info("")
        logger.info("=" * 80)
        logger.info("Planning Phase Complete")
        logger.info("=" * 80)
        logger.info("")

        return {"planning_results": planning_results}

    @staticmethod
    def _extract_specs_section(spec: str) -> str:
        """Extract the content of 'section Specs ... end Specs' from a spec file.

        Returns the matched block (including the section header/footer) if found,
        otherwise returns the full spec as fallback.
        """
        import re
        m = re.search(r"(section Specs\b.*?^end Specs)", spec, re.DOTALL | re.MULTILINE)
        return m.group(1).strip() if m else spec

    @shutdown_boundary("before specgen generate step")
    @DBOS.step()
    async def _generate_node(self, state: SpecAgentState) -> dict:
        """Generate or refine the specification using LLM with tools."""

        # OPTIMIZATION: Always start fresh - we only need system prompt + current context
        # No need to keep tool call history from previous attempts
        messages = []

        # Add short stable system prompt
        messages.append(self.create_system_message(self.system_prompt))

        # Build stable user message for caching (combine stable content > 4096 tokens)
        stable_parts = []

        # 1. SpecGen.md remaining content
        stable_parts.append(f"# Guidelines and Requirements\n\n{self.document_content}")

        # 2. Problem description (stable across all attempts for same problem)
        stable_parts.append(f"# Problem to Solve\n\n{state['problem_description']}")

        # 3. Planning results (includes Lean definitions and RAG examples)
        if state.get("planning_results"):
            stable_parts.append(f"# Relevant Lean/Mathlib Definitions and Examples\n\n{state['planning_results']}")
            logger.info("✓ Using cached planning results (Lean + RAG) from _plan_node")
        else:
            logger.info("⚠ No planning results available")

        # 4. Velvet Reference
        stable_parts.append(f"# Velvet Language Reference\n\n{self.velvet_reference}")

        # Combine all stable content into one large user message for caching
        stable_content = "\n\n".join(stable_parts)

        # Add stable content as cached user message
        from langchain_core.messages import HumanMessage
        stable_message = HumanMessage(
            content=[{
                    "type": "text",
                    "text": stable_content,
                    "cache_control": {"type": "ephemeral", "ttl": "1h"},
                }
            ]
        )
        messages.append(stable_message)

        # Build dynamic human message
        message_parts = []

        if state["specgen_attempt"] == 0:
            # First attempt: Just add basic task instruction
            logger.info("Mode: Initial specification generation (with LeanExplore + RAG)")

            # 5. Task instruction
            task_instruction = f"""
# Task

Generate a formal Velvet specification for the above problem and save it using the `write_file` tool.

**CRITICAL: You MUST use the `write_file` tool to save the specification to: {state["output_file"]}**

Follow all the guidelines above, prioritize using existing Lean/Mathlib definitions, and include diverse test cases.

**CRITICAL SEMANTICS REQUIREMENT:**
- {SET_MAX_HEARTBEATS}
- {SET_PP_COERCIONS}
- {SET_LOOM_TERMINATION_TOTAL}
- {SET_LOOM_CHOICE_DEMONIC}
"""
            message_parts.append(task_instruction)
        else:
            # Retry: Add feedback information to the base prompt
            logger.info("Mode: Refinement based on typecheck errors or coach feedback")

            # 5. All previous attempts and feedback
            history = state.get("spec_history", [])
            all_attempts_parts = []

            # Older attempts: show Specs section + feedback
            for entry in history:
                attempt_num = entry.get("attempt", "?")
                parts = [f"### Attempt {attempt_num}"]
                if entry.get("spec"):
                    specs_section = self._extract_specs_section(entry["spec"])
                    parts.append(f"**Specification (Specs section):**\n{lean_block(specs_section)}")
                if not entry.get("typechecks", True) and entry.get("build_log"):
                    parts.append(f"**Typecheck Errors:**\n{code_block(entry['build_log'])}")
                if entry.get("coach_feedback"):
                    parts.append(f"**Feedback:**\n{entry['coach_feedback']}")
                all_attempts_parts.append("\n\n".join(parts))

            # Latest (current) attempt: show full spec + feedback
            current_parts = [f"### Attempt {state['specgen_attempt']} (most recent)"]
            if state.get("current_spec"):
                current_parts.append(
                    f"**Specification:**\n{lean_block(state['current_spec'])}"
                )
            if not state.get("typechecks", False) and state.get("build_log"):
                current_parts.append(
                    f"**Typecheck Errors:**\n{code_block(state['build_log'])}"
                )
            if state.get("coach_feedback") and state.get("coach_verdict") != CoachVerdict.PENDING:
                current_parts.append(f"**Feedback:**\n{state['coach_feedback']}")
            all_attempts_parts.append("\n\n".join(current_parts))

            if all_attempts_parts:
                header = f"# Previous Attempts and Feedback ({len(all_attempts_parts)} attempt(s))"
                message_parts.append(header + "\n\n" + "\n\n---\n\n".join(all_attempts_parts))

            # 6. Task instruction for retry
            task_instruction = f"""
# Task

Fix the issues in the previous specification and save the corrected version using the `write_file` tool.

**CRITICAL: You MUST use the `write_file` tool to save the corrected specification to: {state["output_file"]}**

**CRITICAL FORMAT REQUIREMENTS (DO NOT REMOVE):**
1. **Required imports** — MUST include at the top:
   - import Velvet.Std
   - import Extensions.Tactics
   - import Extensions.SpecDSL
   - import Extensions.VelvetPBT
   - Add any Mathlib imports if using Mathlib definitions (e.g., import Mathlib.Data.List.Sort)

2. **Required options** — MUST include after imports:
   - {SET_MAX_HEARTBEATS}
   - {SET_PP_COERCIONS}
   - {SET_LOOM_TERMINATION_TOTAL}
   - {SET_LOOM_CHOICE_DEMONIC}

3. **Test case format** — Expected outputs MUST use capital 'E': `test1_Expected`, NOT `test1_expected`

4. **Recommendation line** — MUST include at end of TestCases section:
   - "-- Recommend to validate: X, Y, Z"

Address all typecheck errors and coach feedback while following the guidelines and preserving the format requirements.
"""
            message_parts.append(task_instruction)

        # Build final user message and add to messages
        user_content = "\n\n".join(message_parts)
        messages.append(HumanMessage(content=user_content))

        # Log the complete prompt before generation
        phase_name = (
            "Generation Phase - Initial"
            if state["specgen_attempt"] == 0
            else f"Generation Phase - Retry #{state['specgen_attempt']}"
        )
        self._log_llm_prompt(messages, phase=phase_name)

        # Use the common tool-calling loop
        logger.info("")
        logger.info("=" * 80)
        logger.info("GENERATION Phase: Creating Formal Specification")
        logger.info("=" * 80)
        logger.info(
            "Calling LLM with complete context (LeanExplore + RAG + Problem)..."
        )

        output_path = Path(state["output_file"])

        # Set allowed output files for write_file tool (from common.py)
        from tools.common import set_allowed_output_files

        set_allowed_output_files([state["output_file"]])
        logger.info(f"✓ Set write_file restriction to: {state['output_file']}")

        # Record time before LLM call to detect if file was written
        import time

        call_start_time = time.time()

        # Stop immediately after write_file is called to save tokens
        response = await self.invoke_with_tools(
            messages,
            reasoning_level=self._current_attempt_reasoning_level(state),
        )

        # Read the file that was written to get the spec
        # Check both existence AND that it was written after we called the LLM
        if state["output_file"] and output_path.exists():
            # Verify the file was modified after we started the LLM call
            file_mtime = output_path.stat().st_mtime
            if file_mtime < call_start_time:
                logger.error("=" * 80)
                logger.error("❌ FILE WRITE VERIFICATION FAILED")
                logger.error("=" * 80)
                logger.error(f"File exists but was NOT modified by this LLM call!")
                logger.error(f"File mtime: {file_mtime}")
                logger.error(f"Call start: {call_start_time}")
                logger.error(f"This indicates the write_file tool failed silently.")
                logger.error("=" * 80)
                # Treat as if file doesn't exist, trigger fallback
                spec = None
            else:
                spec = Path(state["output_file"]).read_text()
                file_size = Path(state["output_file"]).stat().st_size
                logger.info("")
                logger.info(f"✓ Specification generated successfully")
                logger.info(f"  - Output file: {state['output_file']}")
                logger.info(
                    f"  - File size: {file_size} bytes ({len(spec)} characters)"
                )
                logger.info(f"  - Lines: {len(spec.splitlines())}")
                logger.info("")
                logger.info("=" * 80)
                logger.info("Generation Phase Complete")
                logger.info("=" * 80)
                logger.info("")
        else:
            spec = None

        # Fallback if file wasn't written or verification failed
        if spec is None:
            # Fallback: LLM didn't call the tool, write file manually
            # response.content can be str or list, convert to str
            if isinstance(response.content, list):
                # If content is a list (e.g., tool calls), extract text
                raw_content = "\n".join(str(item) for item in response.content)
            else:
                raw_content = str(response.content)

            logger.warning("Output file not found, LLM didn't call write_file tool")
            logger.info("Attempting to extract Lean code from LLM response")

            # Try to extract Lean code using multiple strategies
            import re

            # Strategy 1: Extract from import to end TestCases (most robust)
            # This handles cases where LLM wraps code in XML tags, markdown, or adds commentary
            import_to_end_match = re.search(
                r"(^import\s+.*?^end TestCases)", raw_content, re.MULTILINE | re.DOTALL
            )
            if import_to_end_match:
                spec = import_to_end_match.group(1).strip()
                logger.info(f"✓ Extracted Lean code from 'import' to 'end TestCases'")
                logger.warning(
                    "⚠ LLM didn't call write_file tool - extracted code manually"
                )

            # Strategy 2: Extract from wrong tool call format: write_file("path", 'content')
            # LLM sometimes outputs this instead of using proper tool calling
            elif write_file_match := re.search(
                r'write_file\s*\(\s*["\']([^"\']+)["\']\s*,\s*["\'](.*)["\']\s*\)',
                raw_content,
                re.DOTALL,
            ):
                spec = write_file_match.group(2).strip()
                logger.info(f"✓ Extracted Lean code from write_file(...) text format")
                logger.warning(
                    "⚠ LLM used text format instead of tool calling - this is incorrect but handled"
                )

            # Strategy 3: Extract from XML-style tags (various tag names)
            elif xml_match := re.search(
                r"<(?:write_file|content|code)>(.*?)</(?:write_file|content|code)>",
                raw_content,
                re.DOTALL,
            ):
                spec = xml_match.group(1).strip()
                logger.info(f"✓ Extracted Lean code from XML tag")
                logger.warning(
                    "⚠ LLM used XML format instead of tool calling - this is incorrect but handled"
                )

            # Strategy 4: Extract from markdown ```lean ... ``` blocks
            elif lean_blocks := re.findall(
                r"```lean\s*\n(.*?)\n```", raw_content, re.DOTALL
            ):
                spec = lean_blocks[
                    -1
                ].strip()  # Use last block (in case LLM corrects itself)
                logger.info(
                    f"✓ Extracted Lean code from markdown block (using last of {len(lean_blocks)} blocks)"
                )

            # Strategy 5: Check if response starts with "import" (might be raw Lean code)
            elif raw_content.strip().startswith("import"):
                spec = raw_content.strip()
                logger.info(f"✓ Using raw response as Lean code (starts with 'import')")

            # Strategy 6: Last resort - use entire response
            else:
                spec = raw_content
                logger.error("=" * 80)
                logger.error("❌ FAILED TO EXTRACT LEAN CODE")
                logger.error("=" * 80)
                logger.error("Could not extract clean Lean code from LLM response")
                logger.error(
                    "The file will contain LLM commentary and will likely fail to compile"
                )
                logger.error("")
                logger.error("Response preview:")
                logger.error("-" * 40)
                logger.error(raw_content[:500])
                logger.error("-" * 40)
                logger.error("=" * 80)

            # Manually write the file
            output_path = Path(state["output_file"])
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(spec)

            file_size = output_path.stat().st_size
            logger.info(f"✓ Specification written manually")
            logger.info(f"  - Output file: {state['output_file']}")
            logger.info(f"  - File size: {file_size} bytes ({len(spec)} characters)")
            logger.info(f"  - Lines: {len(spec.splitlines())}")

        # OPTIMIZATION: Don't return messages - we don't need the tool call history
        # Next iteration will start fresh with just the spec file content
        result = {
            "current_spec": spec,
            "specgen_attempt": state["specgen_attempt"] + 1,
            # messages are intentionally not included
        }
        return result


def validate_specgen_output(output_content: str) -> ValidationResult:
    """Validate output from SpecGen agent.

    Required sections: Specs, Impl, TestCases
    """
    required = ["Specs", "Impl", "TestCases"]

    try:
        output = LeanFile.from_content(output_content)
    except ValueError as e:
        return ValidationResult.error(f"Failed to parse output as LeanFile: {e}")

    missing = [s for s in required if not output.has_section(s)]
    if missing:
        return ValidationResult.error(
            f"SpecGen output missing required sections: {missing}\n"
            f"Found sections: {output.section_names()}"
        )

    prologue = output.prologue
    if SET_LOOM_TERMINATION_TOTAL not in prologue:
        return ValidationResult.error(
            "SpecGen output must set total correctness semantics: "
            f"missing `{SET_LOOM_TERMINATION_TOTAL}` in prologue"
        )

    if SET_LOOM_CHOICE_DEMONIC not in prologue:
        return ValidationResult.error(
            "SpecGen output must set demonic choice semantics: "
            f"missing `{SET_LOOM_CHOICE_DEMONIC}` in prologue"
        )

    if SET_MAX_HEARTBEATS not in prologue:
        return ValidationResult.error(
            "SpecGen output must set the heartbeat budget in the prologue: "
            f"missing `{SET_MAX_HEARTBEATS}`"
        )

    if SET_PP_COERCIONS not in prologue:
        return ValidationResult.error(
            "SpecGen output must show coercions in the prologue: "
            f"missing `{SET_PP_COERCIONS}`"
        )

    return ValidationResult.ok()
