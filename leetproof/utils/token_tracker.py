"""Token usage tracking for LLM calls."""
import asyncio
import json
from functools import wraps
from pathlib import Path
from typing import Any, Dict, Optional, Callable
from langchain_core.callbacks import BaseCallbackHandler
from langchain_core.outputs import LLMResult
from config.constants import SESSIONS_DIR
from logging_config import get_logger

logger = get_logger(__name__)

# Pricing cache
_pricing_data: Optional[Dict] = None


def _load_pricing() -> Dict:
    """Load model pricing from config file."""
    global _pricing_data
    if _pricing_data is not None:
        return _pricing_data

    import os
    base = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))
    pricing_file = base / "config" / "model_pricing.json"
    if pricing_file.exists():
        with open(pricing_file) as f:
            _pricing_data = json.load(f)
    else:
        _pricing_data = {}
    return _pricing_data


def _get_model_pricing(model_name: str) -> Optional[Dict]:
    """Get pricing for a model using prefix matching."""
    pricing = _load_pricing()
    if not model_name:
        return None

    # Try exact match first
    if model_name in pricing:
        return pricing[model_name]

    # Try prefix match (longest prefix wins)
    best_match = None
    best_len = 0
    for prefix in pricing:
        if model_name.startswith(prefix) and len(prefix) > best_len:
            best_match = prefix
            best_len = len(prefix)

    if best_match:
        return pricing[best_match]
    return None


def compute_cost(
    input_tokens: int,
    output_tokens: int,
    cache_read_tokens: int,
    cache_write_tokens: int,
    model_name: str,
) -> Optional[float]:
    """Compute cost in dollars for token usage."""
    pricing = _get_model_pricing(model_name)
    if not pricing:
        return None

    # LangChain usage_metadata.input_tokens is a gross input count for Anthropic:
    # uncached input + cache reads + cache writes. Charge regular input only for
    # the uncached portion, then add cache-specific prices separately.
    non_cached_input = max(0, input_tokens - cache_read_tokens - cache_write_tokens)

    cost = 0.0
    cost += (non_cached_input / 1_000_000) * pricing["input_per_million"]
    cost += (output_tokens / 1_000_000) * pricing["output_per_million"]

    if cache_read_tokens > 0 and pricing.get("cache_read_per_million"):
        cost += (cache_read_tokens / 1_000_000) * pricing["cache_read_per_million"]

    if cache_write_tokens > 0 and pricing.get("cache_write_per_million"):
        cost += (cache_write_tokens / 1_000_000) * pricing["cache_write_per_million"]

    return cost


class TokenLimitExceededError(Exception):
    """Raised when token usage exceeds configured limits."""

    def __init__(
        self,
        limit_type: str,
        current: int,
        limit: int,
        message: Optional[str] = None
    ):
        self.limit_type = limit_type
        self.current = current
        self.limit = limit
        if message is None:
            message = f"Token limit exceeded: {limit_type} tokens ({current:,}) exceeded limit ({limit:,})"
        super().__init__(message)


class CostLimitExceededError(Exception):
    """Raised when cost exceeds configured limit."""

    def __init__(
        self,
        current: float,
        limit: float,
        message: Optional[str] = None
    ):
        self.current = current
        self.limit = limit
        if message is None:
            message = f"Cost limit exceeded: ${current:.4f} exceeded limit ${limit:.2f}"
        super().__init__(message)

# Current agent context for per-agent tracking
_current_agent: Optional[str] = None
_current_status: str = "Starting"
_current_file: Optional[str] = None

# TUI app reference for live updates
_tui_app: Optional[Any] = None


def set_tui_app(app: Any) -> None:
    """Set the TUI app instance for live updates."""
    global _tui_app
    _tui_app = app


def get_tui_app() -> Optional[Any]:
    """Get the TUI app instance."""
    return _tui_app


def _update_tui_status() -> None:
    """Push current status to TUI."""
    if _tui_app is not None:
        try:
            _tui_app.call_from_thread(
                _tui_app.update_status,
                _current_agent or "Initializing",
                _current_status,
                _current_file
            )
        except Exception:
            pass


def set_current_agent(agent_name: str, status: str = "Running") -> None:
    """Set the current agent for token tracking and update TUI."""
    global _current_agent, _current_status
    _current_agent = agent_name
    _current_status = status
    _update_tui_status()


def get_current_agent() -> Optional[str]:
    """Get the current agent name."""
    return _current_agent


def set_status(status_text: str) -> None:
    """Set the current status and update TUI."""
    global _current_status
    _current_status = status_text
    _update_tui_status()


def set_current_file(file_path: Optional[str]) -> None:
    """Set the current file being worked on and update TUI."""
    global _current_file
    _current_file = file_path
    _update_tui_status()


def get_current_file() -> Optional[str]:
    """Get the current file being worked on."""
    return _current_file


class status:
    """Context manager for setting status during an operation.

    Usage:
        with status("Typechecking"):
            run_typecheck()

        with status("Calling LLM"):
            response = await llm.ainvoke(messages)
    """

    def __init__(self, status_text: str):
        self.status_text = status_text
        self.previous_status: Optional[str] = None

    def __enter__(self):
        global _current_status
        self.previous_status = _current_status
        set_status(self.status_text)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        set_status(self.previous_status or "Running")
        return False

    async def __aenter__(self):
        return self.__enter__()

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        return self.__exit__(exc_type, exc_val, exc_tb)


def with_status(status_text: str) -> Callable:
    """Decorator for setting status during a function call.

    Usage:
        @with_status("Typechecking")
        def _run_typecheck(self, state):
            ...

        @with_status("Calling LLM")
        async def ainvoke_llm(self, messages):
            ...
    """
    def decorator(func: Callable) -> Callable:
        if asyncio.iscoroutinefunction(func):
            @wraps(func)
            async def async_wrapper(*args, **kwargs):
                with status(status_text):
                    return await func(*args, **kwargs)
            return async_wrapper
        else:
            @wraps(func)
            def sync_wrapper(*args, **kwargs):
                with status(status_text):
                    return func(*args, **kwargs)
            return sync_wrapper
    return decorator


class TokenUsageTracker(BaseCallbackHandler):
    """Callback handler to track token usage across LLM calls."""

    def __init__(
        self,
        session_name: Optional[str] = None,
        max_input_tokens: Optional[int] = None,
        max_output_tokens: Optional[int] = None,
        max_total_tokens: Optional[int] = None,
        max_cost: Optional[float] = None,
        model_name: Optional[str] = None,
    ):
        super().__init__()
        self.total_tokens = 0
        self.total_prompt_tokens = 0
        self.total_completion_tokens = 0
        self.call_count = 0
        # Cache tracking (vendor-agnostic)
        self.total_cache_read_tokens = 0   # Tokens read from cache (cache hits)
        self.total_cache_write_tokens = 0  # Tokens written to cache (Anthropic only)
        # Reasoning/thinking token tracking
        self.total_reasoning_tokens = 0    # Tokens used for chain-of-thought reasoning
        # Per-agent tracking
        self.agent_usage: Dict[str, Dict[str, int]] = {}
        # Session name for saving results
        self.session_name = session_name
        # Token limits (None means unlimited)
        self.max_input_tokens = max_input_tokens
        self.max_output_tokens = max_output_tokens
        self.max_total_tokens = max_total_tokens
        # Cost limit (None means unlimited)
        self.max_cost = max_cost
        # Model name for cost calculation
        self.model_name = model_name
        self.total_cost = 0.0
        # Post-call limit breaches trigger graceful shutdown instead of immediate abort.
        # Pre-call checks still raise hard exceptions to block new paid LLM calls.
        self.pending_limit_breach: Optional[Dict[str, Any]] = None

    def on_llm_end(
        self,
        response: LLMResult,
        *,
        run_id: Any = None,
        parent_run_id: Any = None,
        **kwargs: Any,
    ) -> None:
        """Track token usage when LLM call completes."""
        prompt_tokens = 0
        completion_tokens = 0
        total = 0
        cache_read_tokens = 0
        cache_write_tokens = 0
        reasoning_tokens = 0

        # Method 1: Check AIMessage.usage_metadata (standardized in LangChain)
        if response.generations and len(response.generations) > 0:
            for generation_list in response.generations:
                if generation_list and len(generation_list) > 0:
                    gen = generation_list[0]
                    if not hasattr(gen, 'message'):
                        continue
                    message = gen.message
                    # Debug: print full response metadata
                    if hasattr(message, 'response_metadata'):
                        logger.info(f"[DEBUG] response_metadata: {message.response_metadata}")
                    if hasattr(message, 'usage_metadata') and message.usage_metadata:
                        usage: dict = message.usage_metadata  # type: ignore[assignment]
                        logger.info(f"[DEBUG] usage_metadata: {usage}")
                        prompt_tokens = usage.get("input_tokens", 0)
                        completion_tokens = usage.get("output_tokens", 0)
                        total = usage.get("total_tokens", prompt_tokens + completion_tokens)

                        # Cache tokens (uniform for OpenAI and Anthropic via input_token_details)
                        input_details = usage.get("input_token_details", {})
                        if input_details:
                            cache_read_tokens = input_details.get("cache_read", 0)
                            cache_write_tokens = input_details.get("cache_creation", 0)

                        # Reasoning/thinking tokens (uniform across providers via output_token_details)
                        output_details = usage.get("output_token_details", {})
                        if output_details:
                            reasoning_tokens = output_details.get("reasoning", 0)
                        break

        # Method 2: Check llm_output (fallback for older providers)
        if total == 0 and response.llm_output:
            # OpenAI/Anthropic/Cerebras/Groq format
            token_usage = response.llm_output.get("token_usage", {})

            if not token_usage:
                # Alternative key
                token_usage = response.llm_output.get("usage", {})

            if not token_usage:
                # Google legacy format
                usage_metadata = response.llm_output.get("usage_metadata", {})
                if usage_metadata:
                    token_usage = {
                        "prompt_tokens": usage_metadata.get("prompt_token_count", 0),
                        "completion_tokens": usage_metadata.get("candidates_token_count", 0),
                        "total_tokens": usage_metadata.get("total_token_count", 0)
                    }

            prompt_tokens = token_usage.get("prompt_tokens", 0)
            completion_tokens = token_usage.get("completion_tokens", 0)
            total = token_usage.get("total_tokens", prompt_tokens + completion_tokens)

            # OpenAI cache tokens (in prompt_tokens_details)
            prompt_details = token_usage.get("prompt_tokens_details", {})
            logger.debug(f"token_usage keys: {token_usage.keys() if hasattr(token_usage, 'keys') else token_usage}")
            logger.debug(f"prompt_tokens_details: {prompt_details}")
            if prompt_details:
                cache_read_tokens = prompt_details.get("cached_tokens", 0)

            # Anthropic cache tokens (in usage dict directly)
            if cache_read_tokens == 0:
                cache_read_tokens = token_usage.get("cache_read_input_tokens", 0)
                cache_write_tokens = token_usage.get("cache_creation_input_tokens", 0)

            # Reasoning tokens (fallback path)
            if reasoning_tokens == 0:
                # OpenAI: completion_tokens_details.reasoning_tokens
                completion_details = token_usage.get("completion_tokens_details", {})
                if completion_details:
                    reasoning_tokens = completion_details.get("reasoning_tokens", 0)

        if total > 0:
            self.call_count += 1

            # Get current agent
            agent_name = get_current_agent() or "unknown"

            # Log this individual call
            logger.info("─" * 60)
            logger.info(f"LLM Call #{self.call_count} ({agent_name}) Token Usage:")
            logger.info(f"  Input Tokens:  {prompt_tokens:,}")
            logger.info(f"  Output Tokens: {completion_tokens:,}")
            logger.info(f"  Total Tokens:  {total:,}")
            if cache_read_tokens > 0 or cache_write_tokens > 0:
                logger.info(f"  Cache Read:    {cache_read_tokens:,} {'✓ HIT' if cache_read_tokens > 0 else ''}")
                logger.info(f"  Cache Write:   {cache_write_tokens:,}")
            if reasoning_tokens > 0:
                logger.info(f"  Reasoning:     {reasoning_tokens:,} (of {completion_tokens:,} output)")
            logger.info("─" * 60)

            # Update global totals
            self.total_prompt_tokens += prompt_tokens
            self.total_completion_tokens += completion_tokens
            self.total_tokens += total
            self.total_cache_read_tokens += cache_read_tokens
            self.total_cache_write_tokens += cache_write_tokens
            self.total_reasoning_tokens += reasoning_tokens

            # Update cost
            if self.model_name:
                call_cost = compute_cost(
                    prompt_tokens, completion_tokens,
                    cache_read_tokens, cache_write_tokens,
                    self.model_name
                )
                if call_cost is not None:
                    self.total_cost += call_cost
                    logger.info(f"  Cost:          ${call_cost:.4f} (total: ${self.total_cost:.4f})")

            # Update per-agent totals
            if agent_name not in self.agent_usage:
                self.agent_usage[agent_name] = {
                    "call_count": 0,
                    "prompt_tokens": 0,
                    "completion_tokens": 0,
                    "total_tokens": 0,
                    "cache_read_tokens": 0,
                    "cache_write_tokens": 0,
                    "reasoning_tokens": 0,
                }
            self.agent_usage[agent_name]["call_count"] += 1
            self.agent_usage[agent_name]["prompt_tokens"] += prompt_tokens
            self.agent_usage[agent_name]["completion_tokens"] += completion_tokens
            self.agent_usage[agent_name]["total_tokens"] += total
            self.agent_usage[agent_name]["cache_read_tokens"] += cache_read_tokens
            self.agent_usage[agent_name]["cache_write_tokens"] += cache_write_tokens
            self.agent_usage[agent_name]["reasoning_tokens"] += reasoning_tokens

            # Update TUI if available
            self._update_tui()

            # Check token limits
            self._check_limits()

    def _update_tui(self) -> None:
        """Update TUI with current token counts and per-agent breakdown."""
        tui_app = get_tui_app()
        if tui_app is not None:
            try:
                tui_app.call_from_thread(
                    tui_app.update_tokens,
                    self.total_prompt_tokens,
                    self.total_completion_tokens,
                    self.total_tokens,
                    self.max_input_tokens,
                    self.max_output_tokens,
                    self.max_total_tokens,
                    self.agent_usage,  # Pass per-agent breakdown
                    self.total_cache_read_tokens,
                    self.total_cache_write_tokens,
                    self.total_cost,
                )
                tui_app.call_from_thread(
                    tui_app.update_llm_calls,
                    self.call_count
                )
            except Exception:
                pass  # Don't break if TUI update fails

    def check_limits_before_call(self) -> None:
        """Check if any limits have already been exceeded before making an LLM call.

        Normally this prevents new LLM calls when limits are already exceeded.
        Once a graceful shutdown has already been requested, we stop enforcing
        pre-call limits here and let the current DBOS/langgraph unit finish.
        The shutdown boundary is responsible for exiting cleanly.
        """
        from utils.shutdown import is_shutdown_requested

        if is_shutdown_requested():
            logger.info(
                "Shutdown already requested; skipping pre-call limit enforcement until "
                "the next graceful shutdown boundary"
            )
            return

        if self.max_input_tokens is not None and self.total_prompt_tokens >= self.max_input_tokens:
            logger.error(f"Input token limit already exceeded: {self.total_prompt_tokens:,} >= {self.max_input_tokens:,}")
            raise TokenLimitExceededError(
                limit_type="input",
                current=self.total_prompt_tokens,
                limit=self.max_input_tokens
            )

        if self.max_output_tokens is not None and self.total_completion_tokens >= self.max_output_tokens:
            logger.error(f"Output token limit already exceeded: {self.total_completion_tokens:,} >= {self.max_output_tokens:,}")
            raise TokenLimitExceededError(
                limit_type="output",
                current=self.total_completion_tokens,
                limit=self.max_output_tokens
            )

        if self.max_total_tokens is not None and self.total_tokens >= self.max_total_tokens:
            logger.error(f"Total token limit already exceeded: {self.total_tokens:,} >= {self.max_total_tokens:,}")
            raise TokenLimitExceededError(
                limit_type="total",
                current=self.total_tokens,
                limit=self.max_total_tokens
            )

        if self.max_cost is not None and self.total_cost >= self.max_cost:
            logger.error(f"Cost limit already exceeded: ${self.total_cost:.4f} >= ${self.max_cost:.2f}")
            raise CostLimitExceededError(
                current=self.total_cost,
                limit=self.max_cost
            )

    def _set_pending_limit_breach(self, kind: str, current: int | float, limit: int | float, message: str) -> None:
        """Record a post-call limit breach for graceful shutdown handling."""
        if self.pending_limit_breach is None:
            self.pending_limit_breach = {
                "kind": kind,
                "current": current,
                "limit": limit,
                "message": message,
            }

    def get_pending_limit_breach(self) -> Optional[Dict[str, Any]]:
        """Return the currently pending post-call limit breach, if any."""
        return self.pending_limit_breach

    def consume_pending_limit_breach(self) -> Optional[Dict[str, Any]]:
        """Return and clear the currently pending post-call limit breach, if any."""
        breach = self.pending_limit_breach
        self.pending_limit_breach = None
        return breach

    def _check_limits(self) -> None:
        """Check if any token limits have been exceeded after a completed LLM call.

        Post-call breaches do not raise immediately. Instead, we remember the
        first breach and let higher layers request a graceful shutdown after the
        current unit of work finishes.
        """
        if self.max_input_tokens is not None and self.total_prompt_tokens > self.max_input_tokens:
            message = (
                f"Token limit exceeded: input tokens ({self.total_prompt_tokens:,}) "
                f"exceeded limit ({self.max_input_tokens:,})"
            )
            logger.error(f"Input token limit exceeded: {self.total_prompt_tokens:,} > {self.max_input_tokens:,}")
            self._set_pending_limit_breach(
                kind="input_tokens",
                current=self.total_prompt_tokens,
                limit=self.max_input_tokens,
                message=message,
            )
            return

        if self.max_output_tokens is not None and self.total_completion_tokens > self.max_output_tokens:
            message = (
                f"Token limit exceeded: output tokens ({self.total_completion_tokens:,}) "
                f"exceeded limit ({self.max_output_tokens:,})"
            )
            logger.error(f"Output token limit exceeded: {self.total_completion_tokens:,} > {self.max_output_tokens:,}")
            self._set_pending_limit_breach(
                kind="output_tokens",
                current=self.total_completion_tokens,
                limit=self.max_output_tokens,
                message=message,
            )
            return

        if self.max_total_tokens is not None and self.total_tokens > self.max_total_tokens:
            message = (
                f"Token limit exceeded: total tokens ({self.total_tokens:,}) "
                f"exceeded limit ({self.max_total_tokens:,})"
            )
            logger.error(f"Total token limit exceeded: {self.total_tokens:,} > {self.max_total_tokens:,}")
            self._set_pending_limit_breach(
                kind="total_tokens",
                current=self.total_tokens,
                limit=self.max_total_tokens,
                message=message,
            )
            return

        if self.max_cost is not None and self.total_cost > self.max_cost:
            message = f"Cost limit exceeded: ${self.total_cost:.4f} exceeded limit ${self.max_cost:.2f}"
            logger.error(f"Cost limit exceeded: ${self.total_cost:.4f} > ${self.max_cost:.2f}")
            self._set_pending_limit_breach(
                kind="cost",
                current=self.total_cost,
                limit=self.max_cost,
                message=message,
            )

    def log_summary(self) -> None:
        """Log a summary of all token usage and save to session."""
        logger.info("")
        logger.info("=" * 60)
        logger.info("FINAL TOKEN USAGE SUMMARY")
        logger.info("=" * 60)
        logger.info(f"Total LLM Calls:        {self.call_count}")
        logger.info(f"Total Input Tokens:     {self.total_prompt_tokens:,}")
        logger.info(f"Total Output Tokens:    {self.total_completion_tokens:,}")
        logger.info(f"Total Tokens:           {self.total_tokens:,}")
        if self.total_cache_read_tokens > 0 or self.total_cache_write_tokens > 0:
            logger.info(f"Total Cache Read:       {self.total_cache_read_tokens:,}")
            logger.info(f"Total Cache Write:      {self.total_cache_write_tokens:,}")
            cache_hit_ratio = (self.total_cache_read_tokens / self.total_prompt_tokens * 100) if self.total_prompt_tokens > 0 else 0
            logger.info(f"Cache Hit Ratio:        {cache_hit_ratio:.1f}%")
        if self.total_reasoning_tokens > 0:
            logger.info(f"Total Reasoning Tokens: {self.total_reasoning_tokens:,}")

        # Log cost if available
        if self.total_cost > 0:
            logger.info(f"Total Cost:             ${self.total_cost:.4f}")

        # Log per-agent breakdown
        if self.agent_usage:
            logger.info("")
            logger.info("Per-Agent Breakdown:")
            for agent_name, usage in sorted(self.agent_usage.items()):
                logger.info(f"  {agent_name}:")
                cache_info = ""
                cache_read = usage.get('cache_read_tokens', 0)
                cache_write = usage.get('cache_write_tokens', 0)
                if cache_read > 0 or cache_write > 0:
                    cache_info = f", cache_read: {cache_read:,}, cache_write: {cache_write:,}"
                reasoning = usage.get('reasoning_tokens', 0)
                reasoning_info = f", reasoning: {reasoning:,}" if reasoning > 0 else ""
                logger.info(f"    Calls: {usage['call_count']}, Tokens: {usage['total_tokens']:,} (in: {usage['prompt_tokens']:,}, out: {usage['completion_tokens']:,}{cache_info}{reasoning_info})")

        logger.info("=" * 60)

        # Save to session file
        self._save_to_session()

    def _save_to_session(self) -> None:
        """Save token usage to session directory."""
        if not self.session_name:
            logger.debug("No session name configured, skipping token usage save")
            return

        try:
            session_dir = Path(SESSIONS_DIR) / self.session_name
            session_dir.mkdir(parents=True, exist_ok=True)

            usage_data = {
                "total": {
                    "call_count": self.call_count,
                    "prompt_tokens": self.total_prompt_tokens,
                    "completion_tokens": self.total_completion_tokens,
                    "total_tokens": self.total_tokens,
                    "cache_read_tokens": self.total_cache_read_tokens,
                    "cache_write_tokens": self.total_cache_write_tokens,
                    "reasoning_tokens": self.total_reasoning_tokens,
                    "cost_usd": self.total_cost,
                    "model": self.model_name,
                },
                "by_agent": self.agent_usage
            }

            usage_file = session_dir / "token_usage.json"
            with open(usage_file, 'w') as f:
                json.dump(usage_data, f, indent=2)

            logger.info(f"Token usage saved to {usage_file}")
        except Exception as e:
            logger.warning(f"Failed to save token usage: {e}")

    def load_from_session(self) -> bool:
        """Load token usage from session directory to resume tracking.

        Returns:
            True if previous usage was loaded, False otherwise
        """
        if not self.session_name:
            logger.debug("No session name configured, skipping token usage load")
            return False

        usage_file = Path(SESSIONS_DIR) / self.session_name / "token_usage.json"
        if not usage_file.exists():
            logger.debug(f"No previous token usage found at {usage_file}")
            return False

        try:
            with open(usage_file) as f:
                usage_data = json.load(f)

            total = usage_data.get("total", {})
            self.call_count = total.get("call_count", 0)
            self.total_prompt_tokens = total.get("prompt_tokens", 0)
            self.total_completion_tokens = total.get("completion_tokens", 0)
            self.total_tokens = total.get("total_tokens", 0)
            self.total_cache_read_tokens = total.get("cache_read_tokens", 0)
            self.total_cache_write_tokens = total.get("cache_write_tokens", 0)
            self.total_reasoning_tokens = total.get("reasoning_tokens", 0)
            self.total_cost = total.get("cost_usd", 0.0)
            self.agent_usage = usage_data.get("by_agent", {})

            logger.info(
                f"Loaded previous token usage: {self.total_tokens:,} total tokens "
                f"({self.call_count} calls, ${self.total_cost:.4f})"
            )
            return True
        except (json.JSONDecodeError, IOError) as e:
            logger.warning(f"Failed to load token usage: {e}")
            return False


# Global tracker instance
_global_tracker: Optional[TokenUsageTracker] = None


def init_token_tracker(
    session_name: Optional[str] = None,
    max_input_tokens: Optional[int] = None,
    max_output_tokens: Optional[int] = None,
    max_total_tokens: Optional[int] = None,
    max_cost: Optional[float] = None,
    model_name: Optional[str] = None,
    resume: bool = False,
) -> TokenUsageTracker:
    """Initialize the global token tracker with explicit configuration.

    Must be called once at application startup before any LLM calls.

    Args:
        session_name: Session name for saving token usage results
        max_input_tokens: Limit on cumulative input/prompt tokens (None = unlimited)
        max_output_tokens: Limit on cumulative output/completion tokens (None = unlimited)
        max_total_tokens: Limit on cumulative total tokens (None = unlimited)
        max_cost: Limit on cumulative cost in USD (None = unlimited)
        model_name: Model name for cost calculation
        resume: If True, load previous token counts from session (for workflow resumption)

    Returns:
        The initialized TokenUsageTracker instance
    """
    global _global_tracker
    if _global_tracker is not None:
        logger.warning("Token tracker already initialized, returning existing instance")
        return _global_tracker

    # Log configured limits
    limits_configured = []
    if max_input_tokens is not None:
        limits_configured.append(f"input={max_input_tokens:,}")
    if max_output_tokens is not None:
        limits_configured.append(f"output={max_output_tokens:,}")
    if max_total_tokens is not None:
        limits_configured.append(f"total={max_total_tokens:,}")
    if max_cost is not None:
        limits_configured.append(f"cost=${max_cost:.2f}")

    if limits_configured:
        logger.info(f"Limits configured: {', '.join(limits_configured)}")
    else:
        logger.debug("No limits configured (unlimited)")

    _global_tracker = TokenUsageTracker(
        session_name=session_name,
        max_input_tokens=max_input_tokens,
        max_output_tokens=max_output_tokens,
        max_total_tokens=max_total_tokens,
        max_cost=max_cost,
        model_name=model_name,
    )

    # Load previous token counts if resuming
    if resume:
        _global_tracker.load_from_session()

    return _global_tracker


def check_limits_before_llm_call() -> None:
    """Check if limits are already exceeded before making an LLM call.

    This is a convenience function that gets the global tracker and checks limits.
    Should be called before each LLM invocation to prevent calls when limits are exceeded.
    """
    tracker = get_token_tracker()
    tracker.check_limits_before_call()


def get_token_tracker() -> TokenUsageTracker:
    """Get the global token tracker instance.

    Raises:
        RuntimeError: If token tracker not initialized via init_token_tracker()
    """
    if _global_tracker is None:
        raise RuntimeError(
            "Token tracker not initialized. Call init_token_tracker() at startup."
        )
    return _global_tracker


def get_pending_limit_breach() -> Optional[Dict[str, Any]]:
    """Return the current post-call limit breach, if any."""
    return get_token_tracker().get_pending_limit_breach()


def consume_pending_limit_breach() -> Optional[Dict[str, Any]]:
    """Return and clear the current post-call limit breach, if any."""
    return get_token_tracker().consume_pending_limit_breach()


def log_token_usage_on_exit(func: Callable) -> Callable:
    """Decorator that logs token usage summary when function exits.

    Works with both synchronous and asynchronous functions.
    Logs token usage on normal exit, exception, or KeyboardInterrupt.

    Example:
        @log_token_usage_on_exit
        async def async_main():
            # ... your code ...
            pass

        @log_token_usage_on_exit
        def main():
            # ... your code ...
            pass
    """
    if asyncio.iscoroutinefunction(func):
        @wraps(func)
        async def async_wrapper(*args, **kwargs):
            try:
                return await func(*args, **kwargs)
            finally:
                # Always log token usage on exit
                tracker = get_token_tracker()
                tracker.log_summary()
        return async_wrapper
    else:
        @wraps(func)
        def sync_wrapper(*args, **kwargs):
            try:
                return func(*args, **kwargs)
            finally:
                # Always log token usage on exit
                tracker = get_token_tracker()
                tracker.log_summary()
        return sync_wrapper
