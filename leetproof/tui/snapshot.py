"""Typed TUI state snapshot for saving and replaying sessions."""
import json
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional, List, Dict


@dataclass
class TokenSnapshot:
    """Token usage snapshot."""
    call_count: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    total_tokens: int = 0
    cache_read_tokens: int = 0
    cache_write_tokens: int = 0
    cost_usd: float = 0.0
    model: Optional[str] = None
    max_input: Optional[int] = None
    max_output: Optional[int] = None
    max_total: Optional[int] = None


@dataclass
class AgentUsage:
    """Per-agent token usage."""
    call_count: int = 0
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    cache_read_tokens: int = 0
    cache_write_tokens: int = 0


@dataclass
class TUISnapshot:
    """Complete TUI state snapshot for saving/replaying."""
    # Session params
    params: Dict[str, str] = field(default_factory=dict)

    # Token usage
    tokens: TokenSnapshot = field(default_factory=TokenSnapshot)

    # Per-agent breakdown
    agent_usage: Dict[str, AgentUsage] = field(default_factory=dict)

    # Logs
    logs: List[str] = field(default_factory=list)

    # Final status
    status: str = "Running"
    error: Optional[str] = None

    # Timing
    start_time: Optional[str] = None  # ISO format
    end_time: Optional[str] = None    # ISO format
    elapsed_seconds: float = 0.0

    def save(self, session_dir: Path) -> None:
        """Save snapshot to session directory."""
        session_dir.mkdir(parents=True, exist_ok=True)
        state_file = session_dir / "tui_state.json"

        # Convert to dict for JSON serialization
        data = {
            "params": self.params,
            "tokens": asdict(self.tokens),
            "agent_usage": {
                name: asdict(usage) for name, usage in self.agent_usage.items()
            },
            "logs": self.logs,
            "status": self.status,
            "error": self.error,
            "start_time": self.start_time,
            "end_time": self.end_time,
            "elapsed_seconds": self.elapsed_seconds,
        }

        with open(state_file, 'w') as f:
            json.dump(data, f, indent=2, default=str)

    @classmethod
    def load(cls, session_dir: Path) -> "TUISnapshot":
        """Load snapshot from session directory."""
        state_file = session_dir / "tui_state.json"

        with open(state_file, 'r') as f:
            data = json.load(f)

        # Reconstruct typed objects
        tokens = TokenSnapshot(**data.get("tokens", {}))

        agent_usage = {}
        for name, usage_data in data.get("agent_usage", {}).items():
            agent_usage[name] = AgentUsage(**usage_data)

        return cls(
            params=data.get("params", {}),
            tokens=tokens,
            agent_usage=agent_usage,
            logs=data.get("logs", []),
            status=data.get("status", "Unknown"),
            error=data.get("error"),
            start_time=data.get("start_time"),
            end_time=data.get("end_time"),
            elapsed_seconds=data.get("elapsed_seconds", 0.0),
        )

    @classmethod
    def from_tracker(
        cls,
        params: dict,
        tracker,
        logs: List[str],
        error: Optional[Exception] = None,
        start_time: Optional[str] = None,
        end_time: Optional[str] = None,
        elapsed_seconds: float = 0.0,
    ) -> "TUISnapshot":
        """Create snapshot from token tracker and collected data."""
        tokens = TokenSnapshot(
            call_count=tracker.call_count,
            input_tokens=tracker.total_prompt_tokens,
            output_tokens=tracker.total_completion_tokens,
            total_tokens=tracker.total_tokens,
            cache_read_tokens=tracker.total_cache_read_tokens,
            cache_write_tokens=tracker.total_cache_write_tokens,
            cost_usd=tracker.total_cost,
            model=tracker.model_name,
            max_input=tracker.max_input_tokens,
            max_output=tracker.max_output_tokens,
            max_total=tracker.max_total_tokens,
        )

        agent_usage = {}
        for name, usage_data in tracker.agent_usage.items():
            agent_usage[name] = AgentUsage(
                call_count=usage_data.get("call_count", 0),
                prompt_tokens=usage_data.get("prompt_tokens", 0),
                completion_tokens=usage_data.get("completion_tokens", 0),
                total_tokens=usage_data.get("total_tokens", 0),
                cache_read_tokens=usage_data.get("cache_read_tokens", 0),
                cache_write_tokens=usage_data.get("cache_write_tokens", 0),
            )

        return cls(
            params=params,
            tokens=tokens,
            agent_usage=agent_usage,
            logs=logs,
            status="FAILED" if error else "Completed",
            error=str(error) if error else None,
            start_time=start_time,
            end_time=end_time,
            elapsed_seconds=elapsed_seconds,
        )
