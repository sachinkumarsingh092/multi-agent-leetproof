"""Program state abstraction with DBOS-friendly serialization.

This module provides a class-based abstraction for tracking program content
while staying compatible with DBOS state serialization. It keeps disk I/O
explicit and supports lazy initialization without exposing lazy semantics to
API callers.
"""

from __future__ import annotations

from pathlib import Path
from typing import Literal, Optional, TypedDict, overload
import copy

from logging_config import get_logger

logger = get_logger(__name__)


class ProgramState(TypedDict):
    """Serializable program buffer for DBOS workflows.

    The "initialized" flag is internal. Callers should use ProgramBuffer
    methods instead of mutating this dict directly.
    """

    path: str
    current: Optional[str]
    stable: Optional[str]
    initialized: bool


class ProgramBuffer:
    """Class wrapper around ProgramState for ergonomic usage.

    Canonical usage patterns:
    - Update only current content:
      `program_state = ProgramBuffer.from_dict(state["program_state"]).update_current(program)`
    - Update current and promote to stable:
      `program_state = ProgramBuffer.from_dict(state["program_state"]).update_current(program, promote_to_stable=True)`
    - Promote existing current content after successful verification:
      `program_state = ProgramBuffer.from_dict(state["program_state"]).promote_current()`

    Use to_dict() only when no mutation helper is involved.
    """

    def __init__(self, state: ProgramState):
        self._state = state

    @classmethod
    def empty(cls, path: str) -> "ProgramBuffer":
        """Create an empty (lazy) program buffer for a file path."""
        return cls(
            {
                "path": path,
                "current": None,
                "stable": None,
                "initialized": False,
            }
        )

    @classmethod
    def from_content(
        cls,
        path: str,
        content: str,
        *,
        stable: bool = False,
    ) -> "ProgramBuffer":
        """Create a buffer from known content."""
        return cls(
            {
                "path": path,
                "current": content,
                "stable": content if stable else None,
                "initialized": True,
            }
        )

    @classmethod
    def from_dict(cls, state: ProgramState) -> "ProgramBuffer":
        """Wrap an existing ProgramState (e.g., loaded from DBOS).

        Handles migration from the old dict shape where current/stable
        were ProgramSnapshot dicts with 'content', 'source', 'revision'.
        """
        # Migration shim: flatten old snapshot dicts to plain strings
        for key in ("current", "stable"):
            val = state.get(key)
            if isinstance(val, dict) and "content" in val:
                state[key] = val["content"]

        return cls(state)

    def to_dict(self) -> ProgramState:
        """Return a deep copy suitable for DBOS persistence."""
        return copy.deepcopy(self._state)

    @property
    def path(self) -> str:
        return self._state["path"]

    def _ensure_initialized(self) -> None:
        if self._state["initialized"]:
            return

        path = Path(self._state["path"])
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("")
            logger.info(f"Created missing program file: {self._state['path']}")

        content = path.read_text()
        self._state["current"] = content
        self._state["initialized"] = True
        logger.info(f"Initialized program state from disk: {self._state['path']}")

    def get_current(self) -> str:
        """Return current content, lazily initializing from disk if needed."""
        self._ensure_initialized()
        current = self._state["current"]
        if current is None:
            raise ValueError("Program state has no current content")
        return current

    @overload
    def get_stable(self, assert_exists: Literal[True]) -> str: ...

    @overload
    def get_stable(self, assert_exists: Literal[False] = ...) -> Optional[str]: ...

    def get_stable(self, assert_exists: bool = False) -> Optional[str]:
        """Return stable content if available.

        Args:
            assert_exists: If True, raise ValueError when stable content is missing.
        """
        stable = self._state["stable"]
        if assert_exists and not stable:
            raise ValueError(
                f"Stable program content is required but missing for {self._state['path']}"
            )
        return stable

    def sync_from_disk(self) -> ProgramState:
        """Re-read current content from disk and return serialized state.

        Use after external writes (e.g., LLM tool calls, LeanFile.reconstruct_and_write_to_file)
        to bring the buffer back in sync with the file on disk.
        """
        content = Path(self._state["path"]).read_text()
        self._state["current"] = content
        self._state["initialized"] = True
        return self.to_dict()

    def _set_current(self, content: str) -> None:
        self._state["current"] = content
        self._state["initialized"] = True

    def _promote_current_to_stable(self) -> None:
        self._ensure_initialized()
        current = self._state["current"]
        if current is None:
            raise ValueError("Program state has no current content to promote")
        self._state["stable"] = current

    def update_current(
        self,
        content: str,
        *,
        promote_to_stable: bool = False,
    ) -> ProgramState:
        """Set current content, optionally promote, and return serialized state."""
        self._set_current(content)
        if promote_to_stable:
            self._state["stable"] = content
        return self.to_dict()

    def promote_current(self) -> ProgramState:
        """Promote current content to stable and return serialized state."""
        self._promote_current_to_stable()
        return self.to_dict()

    def update_stable(self, content: str) -> ProgramState:
        """Set stable content and return serialized state."""
        self._state["stable"] = content
        self._state["initialized"] = True
        return self.to_dict()
