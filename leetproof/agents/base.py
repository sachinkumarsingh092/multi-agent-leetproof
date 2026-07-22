from abc import ABC, abstractmethod
from typing import Any, Optional, ClassVar, Union, TYPE_CHECKING
import time
import json
from pathlib import Path
from functools import wraps
from langchain_core.language_models import BaseChatModel

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langchain_core.messages import (
    AIMessage,
    BaseMessage,
    ToolMessage,
    HumanMessage,
    SystemMessage,
)
from langgraph.graph import StateGraph
from langgraph.graph.state import CompiledStateGraph

from dbos import DBOS, DBOSConfiguredInstance

from agents.agent_state import VelvetAgentState
from logging_config import get_logger, pretty_dict
from utils.message_constants import (
    AGENT_PROMPT,
    AGENT_CONTEXT,
    AGENT_NAME_FIELD,
    MESSAGE_TYPE_FIELD,
)
from utils.agent_context import get_agent_context
from utils.token_tracker import log_token_usage_on_exit, set_current_agent
from utils.message_helpers import PromptSpec, log_llm_interaction, render_prompt
from utils.prompt_helpers import load_additional_context_files
from tools.common import lean_build_file_helper
from utils.program_state import ProgramBuffer
from utils.analytics.store import AttemptLog, attempt as analytics_attempt

logger = get_logger(__name__)


class BaseAgent(ABC, DBOSConfiguredInstance):
    """Base class for all agents."""

    # Required - subclasses must define
    name: ClassVar[str]
    description: ClassVar[str]
    system_prompt: str

    # Optional overrides
    tools: ClassVar[list] = []

    # Additional context files to load (paths relative to project root or prompts/)
    # Subclasses can override this to provide default context files
    # Example: ["prompts/velvet_documentation.md"]
    additional_context_files: ClassVar[list[str]] = []

    def __init__(
        self,
        config: "LLMConfig",
        config_name: Optional[str] = None,
        reasoning_level: "ReasoningLevel | None" = None,
    ):
        """Initialize with LLM config and optional reasoning level.

        The LLM instance is created lazily on first ainvoke_llm() call.

        Args:
            config: LLM configuration (provider + model).
            config_name: Unique name for DBOS registration. Defaults to class name.
            reasoning_level: Reasoning/thinking level for this agent's LLM calls.
                If None, defaults to ReasoningLevel.NONE.
        """
        from providers import ReasoningLevel as RL

        self._llm_config = config
        self._reasoning_level = reasoning_level if reasoning_level is not None else RL.NONE

        self._llm: Optional[BaseChatModel] = None  # Lazy — created on first use

        self._graph: Optional[CompiledStateGraph] = None
        self._additional_context_content: Optional[str] = None  # Cached loaded content

        # Initialize DBOSConfiguredInstance with unique config_name
        super().__init__(config_name=config_name or self.__class__.__name__)

    @property
    def llm(self) -> BaseChatModel:
        """Lazily create and return the LLM for this agent's default reasoning level."""
        if self._llm is None:
            from providers import get_llm
            self._llm = get_llm(self._llm_config, self._reasoning_level)
        return self._llm

    @llm.setter
    def llm(self, value: Optional[BaseChatModel]):
        self._llm = value

    def _resolve_llm(self, reasoning_level: "ReasoningLevel | None" = None) -> BaseChatModel:
        """Get the LLM for the given reasoning level, or the agent's default."""
        if reasoning_level is not None and reasoning_level != self._reasoning_level:
            from providers import get_llm
            return get_llm(self._llm_config, reasoning_level)
        return self.llm

    def create_system_message(
        self, content: str, message_type: str = AGENT_PROMPT
    ) -> SystemMessage:
        """
        Create a SystemMessage tagged with this agent's name and message type.

        Args:
            content: Message content
            message_type: Type of message (AGENT_PROMPT_NAME or AGENT_CONTEXT_NAME)

        Returns:
            SystemMessage with agent_name and message_type fields, and cache_control
            for Anthropic prompt caching
        """
        if self._llm_config.provider.lower() == "anthropic":
            return SystemMessage(
                content=[{
                    "type": "text",
                    "text": content,
                    "cache_control": {"type": "ephemeral", "ttl": "1h"},
                }],
                **{AGENT_NAME_FIELD: self.name, MESSAGE_TYPE_FIELD: message_type}
            )

        return SystemMessage(
            content=content,
            **{AGENT_NAME_FIELD: self.name, MESSAGE_TYPE_FIELD: message_type}
        )

    def _create_human_message(
        self,
        content: str,
        *,
        cache: bool = False,
    ) -> HumanMessage:
        """Create a HumanMessage with optional provider-aware caching metadata.

        Anthropic supports explicit cache breakpoints on content blocks. For
        providers without block-level caching, this returns a plain text message
        so existing behavior stays unchanged.
        """
        if cache and self._llm_config.provider.lower() == "anthropic":
            return HumanMessage(
                content=[{
                    "type": "text",
                    "text": content,
                    "cache_control": {"type": "ephemeral", "ttl": "1h"},
                }]
            )
        return HumanMessage(content=content)

    def _append_segmented_user_messages(
        self,
        messages: list[BaseMessage],
        *,
        stable_content: str | None = None,
        dynamic_content: str | None = None,
    ) -> None:
        """Append stable and dynamic user prompt segments in order.

        Stable content is emitted as a cacheable HumanMessage when the provider
        supports explicit block caching. Dynamic content remains a plain user
        message. This keeps message order unchanged for providers like OpenAI
        while giving Anthropic a cleaner reusable prefix.
        """
        if stable_content and stable_content.strip():
            messages.append(self._create_human_message(stable_content, cache=True))
        if dynamic_content and dynamic_content.strip():
            messages.append(self._create_human_message(dynamic_content))

    def append_prompt(
        self,
        messages: list[BaseMessage],
        prompt: PromptSpec,
    ) -> None:
        """Append a structured prompt using provider-aware segmentation."""
        parts = render_prompt(prompt)
        self._append_segmented_user_messages(
            messages,
            stable_content=parts.stable,
            dynamic_content=parts.dynamic,
        )

    def _has_message_type(self, messages: list[BaseMessage], message_type: str) -> bool:
        """Check if messages list contains a specific message type for this agent."""
        return any(
            isinstance(msg, SystemMessage)
            and getattr(msg, AGENT_NAME_FIELD, None) == self.name
            and getattr(msg, MESSAGE_TYPE_FIELD, None) == message_type
            for msg in messages
        )

    def has_system_messages(self, messages: list[BaseMessage]) -> bool:
        """Check if messages list already contains this agent's prompt SystemMessage."""
        return self._has_message_type(messages, AGENT_PROMPT)

    def _get_additional_context(self) -> Optional[str]:
        """Get additional context content, loading from files if needed.

        Combines context from multiple sources:
        1. Class-defined additional_context_files
        2. CLI --agent-context (from get_agent_context)

        Returns:
            Combined additional context string, or None if no context available
        """
        context_parts = []

        # Load from class-defined additional_context_files
        if self.additional_context_files:
            # Load and cache the content
            if self._additional_context_content is None:
                self._additional_context_content = load_additional_context_files(
                    self.additional_context_files
                )
            if self._additional_context_content:
                context_parts.append(self._additional_context_content)

        # Also add CLI-provided context
        cli_context = get_agent_context(self.name)
        if cli_context:
            context_parts.append(cli_context)

        if not context_parts:
            return None

        return "\n\n---\n\n".join(context_parts)

    def ensure_system_messages(self, messages: list[BaseMessage]) -> None:
        """
        Ensure SystemMessages are present in the messages list.

        Adds agent's system prompt and optional context if not already present.
        Context is combined from:
        1. Class-defined additional_context_files
        2. CLI --agent-context flag

        Modifies the messages list in-place.
        """
        # Add agent prompt if not present
        if not self._has_message_type(messages, AGENT_PROMPT):
            messages.append(
                self.create_system_message(self.system_prompt, AGENT_PROMPT)
            )

        # Add agent context if available and not already present
        additional_context = self._get_additional_context()
        if additional_context and not self._has_message_type(messages, AGENT_CONTEXT):
            messages.append(
                self.create_system_message(additional_context, AGENT_CONTEXT)
            )

    @abstractmethod
    def build_graph(self) -> StateGraph:
        """Build and return the agent's graph (not compiled).

        Subclasses must implement this to define their workflow.
        """
        pass

    async def get_tools(self) -> list:
        """Get the tools available to this agent.

        Override this method in subclasses to provide custom tools.
        Default implementation returns the tools list.
        """
        return self.tools

    @property
    def graph(self) -> CompiledStateGraph:
        """Get compiled graph, building if needed."""
        if self._graph is None:
            self._graph = self.build_graph().compile()
        return self._graph

    def invoke(self, input: Any, context: Optional[dict] = None) -> Any:
        """Execute the agent's graph."""
        result = self.graph.invoke(input)
        return result

    def stream(self, input: Any, context: Optional[dict] = None):
        """Stream the agent's graph execution."""
        return self.graph.stream(input)

    def as_node(self):
        """Return compiled graph for use as a node in parent workflows.

        Note: DBOS handles state tracking via @DBOS.step() decorated node methods.
        """
        return self.graph

    @abstractmethod
    async def run_workflow(self, state: dict) -> dict:
        """Execute the agent's graph as a DBOS workflow.

        Subclasses must implement this with @DBOS.workflow() decorator
        so that inner @DBOS.step()-decorated graph nodes are independently
        checkpointed. Use no decorator only if the node calls a child
        @DBOS.workflow() (e.g., VelvetProofOrchestratorAgent).

        Args:
            state: Initial state dict

        Returns:
            Final state dict after graph execution
        """
        pass

    # Optional hooks
    def pre_run(self, input: Any, context: Optional[dict] = None) -> Any:
        """Called before run. Can modify input."""
        return input

    def post_run(self, output: Any) -> Any:
        """Called after run. Can modify output."""
        return output

    def _analytics_attempt(
        self,
        state: dict,
        *,
        scope: str | None = None,
        counter_key: str = "attempt",
    ) -> AttemptLog:
        """Bind the current logical analytics attempt for this state."""
        attempt_no = int(state.get(counter_key, 0))
        if attempt_no <= 0:
            raise ValueError(
                f"Analytics attempt number must be positive, got {attempt_no} for counter '{counter_key}'"
            )
        return analytics_attempt(scope or self.name, attempt_no)

    def _save_phase_result(
        self, state: "VelvetAgentState | dict", stable_content: str
    ) -> dict:
        """
        Save this phase's stable content for inter-phase reference.

        Args:
            state: Current state
            stable_content: The proven program content to save

        Returns:
            Update dict with phase_results
        """
        # Store raw content snapshot for lightweight inter-phase sharing.
        phase_results = state.get("phase_results", {}).copy()
        phase_results[self.name] = {"stable_content": stable_content}
        return {"phase_results": phase_results}

    def _run_typecheck(
        self,
        state: VelvetAgentState,
        save_phase_if_stable: bool = True,
    ) -> dict:
        """
        Run typecheck on output_file and update state.

        Reads and typechecks the file at output_file. If successful, saves that
        file's content as stable content in program_state (and optionally to
        phase_results).

        Args:
            state: Current state (must contain 'output_file')
            save_phase_if_stable: Save stable content to phase_results if typecheck passes

        Returns:
            Update dict with: typechecks, diagnostics, program_state (if passed),
            phase_results (if save_phase_if_stable=True)
        """
        output_file = state.get("output_file", "")
        result = lean_build_file_helper(output_file)

        # Build update dict
        update_dict: dict[str, object] = {
            "typechecks": result.typechecks,
            "diagnostics": result.diagnostics,
            "build_log": result.as_string(["error"]),
        }

        # If typecheck passed, read the file we just verified and save it
        if result.typechecks:
            program = Path(output_file).read_text()
            update_dict["program_state"] = ProgramBuffer.from_dict(
                state["program_state"]
            ).update_current(program, promote_to_stable=True)
            # Optionally save to phase_results for other phases
            if save_phase_if_stable:
                update_dict.update(self._save_phase_result(state, program))

        return update_dict

    async def ainvoke_llm(
        self,
        messages: list[BaseMessage],
        log_response: bool = False,
        reasoning_level: "ReasoningLevel | None" = None,
    ) -> AIMessage:
        """Safely invoke LLM with messages.

        Args:
            messages: Messages to send to LLM
            log_response: Whether to log the response content
            reasoning_level: Per-call reasoning override. If None, uses agent default.

        Returns:
            AI response message

        Raises:
            ValueError: If LLM is not set
            TokenLimitExceededError: If token limits are exceeded
            CostLimitExceededError: If cost limits are exceeded
        """
        effective_level = reasoning_level or self._reasoning_level
        llm = self._resolve_llm(reasoning_level)
        logger.info(f"Invoking LLM with reasoning level: {effective_level}")

        # Check limits before making LLM call to prevent exceeding limits
        from utils.token_tracker import check_limits_before_llm_call, TokenLimitExceededError, CostLimitExceededError
        check_limits_before_llm_call()

        set_current_agent(self.name)

        try:
            response = await self._invoke_llm_with_retry(llm, messages, [], 10, 1)
        except (TokenLimitExceededError, CostLimitExceededError) as e:
            # Limit exceptions should fail immediately without retry
            logger.error(f"Limit exceeded in {self.name} agent: {e}")
            raise

        # Convert post-call limit breaches into a graceful shutdown request.
        self._request_shutdown_for_pending_limit_breach()

        # Ensure response is always an AIMessage (some LLMs return strings)
        if isinstance(response, str):
            response = AIMessage(content=response)
        log_llm_interaction(self.name, messages, response)
        # Normalize content to plain string — when reasoning/thinking is
        # enabled, providers return a list of content blocks instead of a
        # string.  Callers expect .content to be a str.
        response.content = self.extract_text(response)
        if log_response:
            logger.info(f"=====================Response==============================")
            logger.info(f"{response.content}")
        return response

    def _request_shutdown_for_pending_limit_breach(self) -> None:
        """Convert a post-call limit breach into a graceful shutdown request."""
        from utils.shutdown import is_shutdown_requested, request_shutdown
        from utils.token_tracker import consume_pending_limit_breach

        breach = consume_pending_limit_breach()
        if breach is None or is_shutdown_requested():
            return

        reason = breach["message"]
        logger.warning(
            f"{self.name} completed the current LLM call after exceeding {breach['kind']}; "
            "requesting graceful shutdown"
        )
        request_shutdown(reason, run_hooks=True)

    @staticmethod
    def extract_text(response: AIMessage) -> str:
        """Extract text content from an AIMessage.

        Handles both plain string content and list-of-blocks content
        (e.g. when thinking/reasoning is enabled, Anthropic returns
        [{"type": "thinking", ...}, {"type": "text", "text": "..."}]).
        """
        content = response.content
        if isinstance(content, str):
            return content
        if isinstance(content, list):
            parts = []
            for block in content:
                if isinstance(block, str):
                    parts.append(block)
                elif isinstance(block, dict) and block.get("type") == "text":
                    parts.append(block.get("text", ""))
            return "\n".join(parts)
        return str(content or "")

    def _validate_tools(self, tools: list) -> list:
        """Filter out invalid tools (those without proper names)."""
        valid_tools = []
        for i, t in enumerate(tools):
            if not hasattr(t, "name"):
                logger.warning(
                    f"Tool at index {i} missing 'name' attribute: {type(t).__name__}"
                )
                continue

            tool_name = getattr(t, "name", None)
            if (
                not tool_name
                or not isinstance(tool_name, str)
                or tool_name.strip() == ""
            ):
                logger.warning(
                    f"Tool at index {i} has invalid name: '{tool_name}' (type: {type(t).__name__})"
                )
                continue

            valid_tools.append(t)

        if len(valid_tools) < len(tools):
            logger.warning(
                f"Filtered out {len(tools) - len(valid_tools)} invalid tool(s)"
            )

        return valid_tools

    async def _invoke_llm_with_retry(
        self,
        llm_with_tools,
        messages: list[BaseMessage],
        valid_tools: list,
        max_retries: int,
        base_delay: float,
        max_hallucination_retries: int = 5,
    ) -> BaseMessage:
        """Invoke LLM with retry logic and tool hallucination handling."""
        hallucination_retries = 0
        call_options = self._provider_call_options()

        for retry in range(max_retries):
            try:
                # Check limits before making LLM call to prevent exceeding limits
                from utils.token_tracker import check_limits_before_llm_call
                check_limits_before_llm_call()

                response = await llm_with_tools.ainvoke(messages, **call_options)
                return response
            except Exception as e:
                # Don't retry on token/cost limit exceptions - they should fail immediately
                from utils.token_tracker import TokenLimitExceededError, CostLimitExceededError
                if isinstance(e, (TokenLimitExceededError, CostLimitExceededError)):
                    logger.error(f"Limit exceeded, not retrying: {e}")
                    raise

                error_str = str(e)
                logger.warning(
                    f"LLM call failed (attempt {retry + 1}/{max_retries}): {error_str}"
                )

                # Handle tool hallucination errors
                if (
                    "attempted to call tool" in error_str
                    and "which was not in request.tools" in error_str
                ):
                    if hallucination_retries < max_hallucination_retries:
                        hallucination_retries += 1
                        logger.error(
                            f"Model tried to call non-existent tool (hallucination retry {hallucination_retries}/{max_hallucination_retries})"
                        )
                        available_tools = [t.name for t in valid_tools]
                        messages.append(
                            HumanMessage(
                                content=f"ERROR: You tried to call a tool that doesn't exist. "
                                f"Available tools: {', '.join(available_tools)}. "
                                f"Only use these exact names. Continue your task without calling invalid tools."
                            )
                        )
                        continue
                    else:
                        logger.error(
                            f"Model continues to hallucinate tools after {max_hallucination_retries} corrections"
                        )
                        raise Exception(
                            f"LLM repeatedly called non-existent tools: {error_str}"
                        ) from e

                # Retry with exponential backoff
                if retry < max_retries - 1:
                    delay = base_delay * (2**retry)
                    logger.info(f"Retrying in {delay:.1f} seconds...")
                    time.sleep(delay)
                else:
                    logger.error(f"All {max_retries} retry attempts failed")
                    raise Exception(
                        f"LLM invocation failed after {max_retries} retries: {str(e)}"
                    ) from e

        # Should not reach here due to raises above
        raise Exception(f"LLM invocation failed after {max_retries} retries")

    def _provider_call_options(self) -> dict[str, Any]:
        """Provider-specific per-call options applied centrally.

        Anthropic supports invocation-time prompt caching, which marks the
        final content block of the final message as a cache breakpoint. This
        gives us incremental caching for tool loops without changing every
        agent's prompt construction. Other providers receive no extra options.
        """
        if self._llm_config.provider.lower() == "anthropic":
            return {"cache_control": {"type": "ephemeral", "ttl": "1h"}}
        return {}

    def _log_llm_response(self, response: BaseMessage, iteration: int) -> None:
        """Log LLM response."""
        if isinstance(response, AIMessage) and response.tool_calls:
            logger.info(
                f"[Iteration {iteration + 1}] LLM requested {len(response.tool_calls)} tool call(s)"
            )
        else:
            # Final response - show preview at INFO, full at DEBUG
            content_preview = response.content[:500] if response.content else ""
            if len(response.content) > 200:
                content_preview += "..."
            logger.info(
                f"[Iteration {iteration + 1}] LLM final response: {content_preview}"
            )
            logger.debug(f"Full response:\n{response.content}")

    async def _execute_tool(self, tool_call: Any, tools: list[Any]) -> str:
        """Execute a single tool call and return the result."""
        tool_name = tool_call["name"]
        tool_args = tool_call["args"]

        logger.info(f"→ {tool_name}")

        # Find and execute the tool
        for tool in tools:
            if tool.name == tool_name:
                try:
                    if hasattr(tool, "ainvoke"):
                        result = await tool.ainvoke(tool_args)
                    else:
                        result = tool.invoke(tool_args)
                    return str(result)
                except Exception as e:
                    error_msg = f"Error executing tool: {str(e)}"
                    logger.error(f"Tool {tool_name} failed: {str(e)}")
                    return error_msg

        # Tool not found
        logger.warning(f"Tool not found: {tool_name}")
        return f"Tool not found: {tool_name}"

    async def invoke_with_tools(
        self,
        messages: list[BaseMessage],
        max_iterations: int = 10,
        max_retry_per_call: int = 5,
        base_delay: float = 1.0,
        max_hallucination_retry_per_call: int = 5,
        reasoning_level: "ReasoningLevel | None" = None,
    ) -> BaseMessage:
        """
        Invoke LLM with tools in a loop until it produces a final response.

        Args:
            messages: Initial messages to send to LLM (modified in place!)
            max_iterations: Maximum number of tool-calling iterations
            max_retry_per_call: Maximum number of retries per LLM call on error
            base_delay: Base delay in seconds for exponential backoff
            max_hallucination_retry_per_call: Maximum number of retries for tool hallucination errors per call
            reasoning_level: Per-call reasoning override. If None, uses agent default.

        Returns:
            The final AI message (without tool calls)
        """
        effective_level = reasoning_level or self._reasoning_level
        llm = self._resolve_llm(reasoning_level)
        logger.info(f"Invoking LLM with tools, reasoning level: {effective_level}")

        set_current_agent(self.name)
        tools = await self.get_tools()
        valid_tools = self._validate_tools(tools)
        llm_with_tools = llm.bind_tools(valid_tools)

        for iteration in range(max_iterations):
            # Call LLM with retry logic
            response = await self._invoke_llm_with_retry(
                llm_with_tools,
                messages,
                valid_tools,
                max_retry_per_call,
                base_delay,
                max_hallucination_retry_per_call,
            )

            log_llm_interaction(self.name, messages, response)
            self._log_llm_response(response, iteration)
            self._request_shutdown_for_pending_limit_breach()

            # Check if we're done (no tool calls)
            if not (isinstance(response, AIMessage) and response.tool_calls):
                return response

            # Add AI response to message history
            messages.append(response)

            # Execute all tool calls
            if isinstance(response, AIMessage):
                for tool_call in response.tool_calls:
                    tool_result = await self._execute_tool(tool_call, tools)

                    # Add tool result to message history
                    messages.append(
                        ToolMessage(
                            content=tool_result,
                            tool_call_id=tool_call["id"],
                            name=tool_call["name"],
                        )
                    )

        # Max iterations reached
        logger.warning(f"Max iterations ({max_iterations}) reached in tool loop")
        response = await llm_with_tools.ainvoke(
            messages, **self._provider_call_options()
        )
        log_llm_interaction(self.name, messages, response)
        self._request_shutdown_for_pending_limit_breach()
        return response

    @classmethod
    @log_token_usage_on_exit
    async def run(
        cls,
        state_file: Optional[str] = None,
        session_name: Optional[str] = None,
    ) -> dict:
        """
        Run the agent standalone, loading state from a file.

        Requires DBOS and container to be initialized first (via main() or _init_dbos_standalone()).

        Args:
            state_file: Path to JSON file containing the serialized state (optional, reads from args if not provided)
            session_name: Session name for output directory (optional, reads from args or uses timestamp)

        Returns:
            The final state after agent execution

        Example state file (state.json):
            {
                "specification": "...",
                "output_file": "/path/to/file.lean",
                "program_state": {"path": "...", "current": null, "stable": null, "initialized": false},
                "attempt": 0,
                "judge_verdict": "PENDING",
                "judge_reasoning": "",
                "build_log": "",
                "typechecks": false
            }

        Usage:
            # Via main() which handles DBOS initialization:
            if __name__ == "__main__":
                MyAgent.main()

            # Or manually with DBOS setup:
            MyAgent._init_dbos_standalone()
            await MyAgent.run(state_file="state.json")
        """
        from args import get_args
        from config.constants import SESSIONS_DIR

        # Get args if parameters not provided
        if state_file is None or session_name is None:
            args = get_args()
            if state_file is None:
                state_file = args.state_file
            if session_name is None:
                session_name = args.session_name

        if not state_file:
            logger.error("--state-file is required for standalone agent execution")
            logger.error("Usage: uv run python -m agents.<agent_module> --state-file <state.json>")
            raise ValueError("state_file is required")

        # Load state from file
        path = Path(state_file)
        if not path.exists():
            raise FileNotFoundError(f"State file not found: {state_file}")

        logger.info(f"Loading state from {state_file}")
        with open(path, "r") as f:
            state = json.load(f)

        # Get agent from container (uses DBOS-registered instance)
        from container import get_container

        container = get_container()
        agent = container.get_agent_by_name(cls.name)
        if agent is None:
            raise RuntimeError(f"Agent '{cls.name}' not found in container")

        logger.info(f"Loaded state with keys: {list(state.keys())}")
        logger.info(f"Invoking agent: {agent.name}")

        # Set write restriction if output_file is in state
        from tools.common import set_allowed_output_files, clear_allowed_output_files

        output_file = state.get("output_file")
        if output_file:
            set_allowed_output_files([output_file])
            logger.info(f"Restricted write_file tool to only: {output_file}")

        try:
            # Use run_workflow for DBOS support (if container was initialized)
            # Otherwise fall back to graph.ainvoke
            final_state = await agent.run_workflow(state)

            logger.info(f"Agent {agent.name} completed")

            # Save output state to session directory
            session_name = session_name or "default"
            session_dir = Path(SESSIONS_DIR) / session_name
            session_dir.mkdir(parents=True, exist_ok=True)

            output_file = session_dir / f"{agent.name}_output.json"

            # Serialize state (skip messages field as it contains non-serializable objects)
            serializable_state = {
                k: v for k, v in final_state.items() if k != "messages"
            }

            with open(output_file, "w") as f:
                json.dump(serializable_state, f, indent=2, default=str)

            logger.info(f"Saved output state to {output_file}")

            print("\n" + "=" * 80)
            print(f"{agent.name.upper()} COMPLETED")
            print("=" * 80)
            print(f"Output saved to: {output_file}")
            print("=" * 80)

            return final_state
        except KeyboardInterrupt:
            logger.info("\nInterrupted by user")
            import sys

            sys.exit(130)  # Standard exit code for SIGINT
        finally:
            # Clear write restriction
            clear_allowed_output_files()

    @classmethod
    def main(cls) -> None:
        """
        CLI entry point for running this agent standalone with TUI support.

        Initializes DBOS and the agent container before running the workflow.
        This ensures proper DBOS registration and recovery support.

        Usage in __main__ block:
            if __name__ == "__main__":
                MyAgent.main()
        """
        from runner import run
        from args import get_args, merge_session_params
        from config.constants import SESSIONS_DIR
        import os
        import sys

        args = get_args()

        # Change to project directory before any relative path resolution
        project_dir = os.path.abspath(args.project)
        if not os.path.isdir(project_dir):
            print(f"Error: --project directory does not exist: {project_dir}")
            sys.exit(1)
        os.chdir(project_dir)

        merge_session_params(args)

        # Validate required args
        if not args.provider:
            print("Error: --provider is required")
            sys.exit(1)
        if not args.model:
            print("Error: --model is required")
            sys.exit(1)

        # Initialize DBOS and container before running
        cls._init_dbos_standalone(
            provider=args.provider,
            model=args.model,
            session_name=args.session_name,
            max_input_tokens=args.max_input_tokens,
            max_output_tokens=args.max_output_tokens,
            max_total_tokens=args.max_total_tokens,
            max_cost=args.max_cost,
            agent_context=args.agent_context,
        )

        async def workflow():
            await cls.run()

        try:
            run(workflow)
        except KeyboardInterrupt:
            sys.exit(130)

    @classmethod
    def _init_dbos_standalone(
        cls,
        provider: str,
        model: str,
        session_name: Optional[str] = None,
        max_input_tokens: Optional[int] = None,
        max_output_tokens: Optional[int] = None,
        max_total_tokens: Optional[int] = None,
        max_cost: Optional[float] = None,
        agent_context: Optional[str] = None,
        skip_container: bool = False,
        resume: bool = False,
    ) -> None:
        """Initialize DBOS for standalone execution.

        This sets up DBOS with SQLite persistence. Optionally initializes
        the full agent container (which imports all agents).

        Args:
            provider: LLM provider name
            model: LLM model name
            session_name: Session name for saving results
            max_input_tokens: Token limit for input tokens
            max_output_tokens: Token limit for output tokens
            max_total_tokens: Token limit for total tokens
            max_cost: Maximum cost in USD
            agent_context: JSON string mapping agent names to context file paths
            skip_container: If True, skip container initialization. Caller must
                create agents manually and call DBOS.launch().
            resume: If True, load previous token counts and state from session
        """
        from dbos import DBOS, DBOSConfig
        from providers import LLMConfig
        from utils.token_tracker import init_token_tracker
        from utils.agent_context import init_agent_context
        from utils.message_helpers import init_message_helpers

        # Initialize token tracker first (needed by LLM callbacks)
        # If resuming, load previous token counts from session
        init_token_tracker(
            session_name=session_name,
            max_input_tokens=max_input_tokens,
            max_output_tokens=max_output_tokens,
            max_total_tokens=max_total_tokens,
            max_cost=max_cost,
            model_name=model,
            resume=resume,
        )

        # Initialize agent context
        init_agent_context(agent_context)

        # Initialize message helpers for LLM interaction logging
        init_message_helpers(session_name)

        # Initialize DBOS with SQLite.
        # Use a deterministic executor_id derived from session_name so that on
        # resume, DBOS's auto-recovery thread can find and recover pending
        # workflows through the proper code path.
        from config.constants import APP_VERSION, DB_DIR
        Path(DB_DIR).mkdir(parents=True, exist_ok=True)
        config: DBOSConfig = {
            "name": f"lloom-{cls.name}",
            "system_database_url": f"sqlite:///{DB_DIR}/lloom_{cls.name}.sqlite",
            "executor_id": f"{cls.name}-{session_name}",
            "application_version": APP_VERSION,
        }
        DBOS(config=config)

        # Optionally initialize full container (imports all agents)
        if not skip_container:
            from container import init_container
            init_container(LLMConfig(provider=provider, model=model))
            # Launch DBOS after container creates all agents
            DBOS.launch()
            logger.info(f"DBOS initialized for standalone {cls.name}")
