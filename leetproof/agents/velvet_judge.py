from typing import Optional, TYPE_CHECKING

from dbos import DBOS
from langchain_core.messages import HumanMessage

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel

from agents.agent_state import JudgeVerdict
from agents.base import BaseAgent
from logging_config import get_logger
from utils.message_helpers import create_prompt, section, stable
from utils.message_constants import AGENT_PROMPT, AGENT_CONTEXT

logger = get_logger(__name__)

JUDGE_EVALUATION_INSTRUCTIONS = """Based on the above information, determine if the agent followed its system prompt correctly and produced valid output.

**Remember**: ANALYZE first, then evaluate, then give your verdict at the END:
```
ANALYSIS:
[What did the agent produce? Any obvious issues?]

CHECKLIST EVALUATION:
- ☐ [Item] → ✅ or ❌ (reason)
...

REASONING:
[Your reasoning]

KEY FINDINGS:
- [Finding 1]
- [Finding 2]

VERDICT: [PASS or FAIL]
```"""


@DBOS.dbos_class()
class VelvetJudgeAgent(BaseAgent):
    """Agent that judges whether another agent followed its system prompt correctly."""

    name = "velvet_judge"
    description = "Judges whether an agent successfully followed its system prompt and completed its task"

    system_prompt: str = ""
    use_tools: bool = True

    def __init__(self, config: "LLMConfig", use_tools: bool = True, reasoning_level: "ReasoningLevel | None" = None):
        super().__init__(config, reasoning_level=reasoning_level)
        self.use_tools = use_tools
        from utils.prompt_helpers import load_system_prompt

        self.system_prompt = load_system_prompt(
            "velvet_judge.md", "You are a judge that evaluates agent outputs."
        )

    def build_graph(self):
        """Not implemented - use evaluate() method directly instead."""
        raise NotImplementedError(
            "VelvetJudgeAgent does not use a graph. Use evaluate() method directly."
        )

    async def run_workflow(self, state: dict) -> dict:
        """Not implemented - use evaluate() method directly instead."""
        raise NotImplementedError(
            "VelvetJudgeAgent does not use run_workflow. Use evaluate() method directly."
        )

    async def _invoke_and_parse(self, messages: list) -> tuple[JudgeVerdict, str]:
        """Invoke LLM and parse the verdict from response."""
        from config.limits import Limits

        if self.use_tools:
            response = await self.invoke_with_tools(
                messages, max_iterations=Limits.VELVET_JUDGE_MAX_ITERATIONS
            )
        else:
            response = await self.ainvoke_llm(messages)

        judgment_text = response.content

        verdict = self._parse_verdict(judgment_text)
        logger.info(f"Verdict: {verdict.value}")
        logger.info(f"Reasoning: {judgment_text}")

        return verdict, judgment_text

    @DBOS.step()
    async def evaluate(
        self,
        agent_name: str,
        agent_system_prompt: str,
        dynamic_ctx: dict[str, str],
        static_ctx: Optional[dict[str, str] | str] = None,
        static_ctx_as_separate_msg: bool = True,
    ) -> tuple[JudgeVerdict, str]:
        """Evaluate an agent's output directly (not via graph).

        Message structure when static_ctx_as_separate_msg=True (default):
        1. System message (AGENT_PROMPT): [Judge's system prompt] + [Agent's system prompt]
        2. System message (AGENT_CONTEXT): Static context (docs)
        3. Human message: Dynamic context (build status, output, etc.)

        Message structure when static_ctx_as_separate_msg=False:
        1. System message (AGENT_PROMPT): [Judge's prompt] + [Static context] + [Agent's prompt]
        2. Human message: Dynamic context

        Caching considerations:
        - When static_ctx_as_separate_msg=True: The static context (e.g., velvet_documentation.md)
          is sent as a separate system message. Since Anthropic's prompt caching works in blocks,
          this allows the SAME static context to be cached and reused across different agents
          (programmer, inferrer, judge) that share the same documentation. This is beneficial
          when static_ctx is large (e.g., full documentation).
        - When static_ctx_as_separate_msg=False: Everything is combined into one system message
          in the order [Judge's prompt] + [Static context] + [Agent's prompt]. This ordering
          ensures the prefix ([Judge's prompt] + [Static context]) is maximally shared across
          different agent evaluations, since only the agent's prompt varies. This may be
          preferable when static_ctx is small.

        Args:
            agent_name: Name of the agent being evaluated
            agent_system_prompt: The agent's system prompt
            dynamic_ctx: Dict with dynamic content (build status, output, etc.)
            static_ctx: Optional static context (docs, etc.).
                Can be a dict of sections or a string.
            static_ctx_as_separate_msg: If True (default), sends static context as a separate
                system message. Better for large static contexts shared across agents.
                If False, combines static context into the main system prompt.

        Returns:
            Tuple of (verdict, reasoning)
        """
        logger.info(f"Evaluating agent: {agent_name}")

        # Build static context string
        if isinstance(static_ctx, dict):
            static_ctx_str = "\n\n".join(f"## {k}\n{v}" for k, v in static_ctx.items())
        elif static_ctx:
            static_ctx_str = static_ctx
        else:
            static_ctx_str = ""

        separator = "\n\n" + "─" * 80 + "\n\n"
        agent_prompt_section = f"# Agent Being Evaluated: {agent_name}\n\n## Agent's System Prompt\n{agent_system_prompt}"

        # Build user message with dynamic context
        evaluation_prompt = create_prompt(
            task=stable("Please evaluate whether the agent successfully followed its system prompt."),
            sections=tuple(section(k, stable(v)) for k, v in dynamic_ctx.items()),
            instructions=stable(JUDGE_EVALUATION_INSTRUCTIONS),
        )

        if static_ctx_as_separate_msg:
            # Separate messages: better for large static contexts shared across agents
            # (e.g., velvet_documentation.md). The static context block can be cached
            # independently and reused by programmer, inferrer, and judge.
            system_prompt_content = separator.join([self.system_prompt, agent_prompt_section])

            messages = [
                self.create_system_message(system_prompt_content, AGENT_PROMPT),
            ]

            if static_ctx_str:
                messages.append(self.create_system_message(static_ctx_str, AGENT_CONTEXT))

            self.append_prompt(messages, evaluation_prompt)
        else:
            # Combined message: [Judge's prompt] + [Static context] + [Agent's prompt]
            # This ordering maximizes the cacheable prefix - [Judge's prompt] + [Static context]
            # remains constant across evaluations of different agents, only the agent's prompt
            # at the end varies. Better for small static contexts.
            system_parts = [self.system_prompt]
            if static_ctx_str:
                system_parts.append(static_ctx_str)
            system_parts.append(agent_prompt_section)

            system_content = separator.join(system_parts)

            messages = [
                self.create_system_message(system_content, AGENT_PROMPT),
            ]
            self.append_prompt(messages, evaluation_prompt)

        return await self._invoke_and_parse(messages)

    def _parse_verdict(self, judgment_text: str) -> JudgeVerdict:
        """
        Parse the verdict from the judge's response.

        Expected format: "VERDICT: PASS" or "VERDICT: FAIL" appears at the end
        of the response (after checklist evaluation and reasoning).
        The parser searches all lines to find the verdict.
        """
        # Look for "VERDICT: PASS" or "VERDICT: FAIL" in the text
        lines = judgment_text.strip().split("\n")

        for line in lines:
            line = line.strip()
            if line.startswith("VERDICT:"):
                verdict_str = line.replace("VERDICT:", "").strip().upper()
                if "PASS" in verdict_str:
                    logger.info("Verdict parsed as PASS")
                    return JudgeVerdict.PASS
                elif "FAIL" in verdict_str:
                    logger.info("Verdict parsed as FAIL")
                    return JudgeVerdict.FAIL

        # If we can't parse it, default to FAIL for safety
        logger.warning(
            f"Could not parse verdict from response, defaulting to FAIL. Response: {judgment_text}"
        )
        return JudgeVerdict.FAIL
