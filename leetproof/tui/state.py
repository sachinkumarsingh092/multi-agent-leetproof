"""Shared state for TUI updates."""
from dataclasses import dataclass, field
from typing import Optional, Callable, List
from threading import Lock


@dataclass
class TUIState:
    """Shared state that the TUI subscribes to for updates."""

    # Agent status
    current_agent: str = "Initializing..."
    status: str = "Starting"

    # Token usage
    input_tokens: int = 0
    output_tokens: int = 0
    total_tokens: int = 0
    max_input_tokens: Optional[int] = None
    max_output_tokens: Optional[int] = None
    max_total_tokens: Optional[int] = None

    # Per-agent token breakdown
    agent_tokens: dict = field(default_factory=dict)

    # Logs buffer
    logs: List[str] = field(default_factory=list)
    max_logs: int = 10000  # Keep last N log lines

    # Callbacks for updates
    _update_callbacks: List[Callable] = field(default_factory=list)
    _lock: Lock = field(default_factory=Lock)

    def add_update_callback(self, callback: Callable) -> None:
        """Register a callback to be called on state updates."""
        with self._lock:
            self._update_callbacks.append(callback)

    def remove_update_callback(self, callback: Callable) -> None:
        """Remove a previously registered callback."""
        with self._lock:
            if callback in self._update_callbacks:
                self._update_callbacks.remove(callback)

    def _notify_update(self) -> None:
        """Notify all registered callbacks of a state update."""
        with self._lock:
            callbacks = self._update_callbacks.copy()
        for callback in callbacks:
            try:
                callback()
            except Exception:
                pass  # Don't let callback errors break the state

    def update_agent(self, agent_name: str, status: Optional[str] = None) -> None:
        """Update current agent info."""
        self.current_agent = agent_name
        if status is not None:
            self.status = status
        self._notify_update()

    def update_tokens(
        self,
        input_tokens: int,
        output_tokens: int,
        total_tokens: int,
        agent_tokens: Optional[dict] = None
    ) -> None:
        """Update token counts."""
        self.input_tokens = input_tokens
        self.output_tokens = output_tokens
        self.total_tokens = total_tokens
        if agent_tokens is not None:
            self.agent_tokens = agent_tokens
        self._notify_update()

    def set_limits(
        self,
        max_input: Optional[int] = None,
        max_output: Optional[int] = None,
        max_total: Optional[int] = None
    ) -> None:
        """Set token limits."""
        self.max_input_tokens = max_input
        self.max_output_tokens = max_output
        self.max_total_tokens = max_total
        self._notify_update()

    def add_log(self, log_line: str) -> None:
        """Add a log line to the buffer."""
        self.logs.append(log_line)
        # Trim if exceeds max
        if len(self.logs) > self.max_logs:
            self.logs = self.logs[-self.max_logs:]
        self._notify_update()

    def get_token_progress(self) -> Optional[float]:
        """Get progress towards token limit (0.0 to 1.0), or None if no limit."""
        if self.max_total_tokens is not None and self.max_total_tokens > 0:
            return min(1.0, self.total_tokens / self.max_total_tokens)
        return None


# Global TUI state instance
_tui_state: Optional[TUIState] = None


def get_tui_state() -> TUIState:
    """Get or create the global TUI state instance."""
    global _tui_state
    if _tui_state is None:
        _tui_state = TUIState()
    return _tui_state


def reset_tui_state() -> None:
    """Reset the global TUI state (useful for testing)."""
    global _tui_state
    _tui_state = None
