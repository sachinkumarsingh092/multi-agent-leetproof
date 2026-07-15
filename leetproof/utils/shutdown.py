"""Global shutdown handling for graceful workflow interruption."""
import asyncio
import threading
from contextlib import contextmanager
from enum import Enum
from functools import wraps
from typing import Optional, Callable
from logging_config import get_logger

logger = get_logger(__name__)

# Global shutdown state
_shutdown_requested = threading.Event()
# We might not want to run shutdown hooks (that do some stuff to handle things gracefully) for all kinds of errors.
# Example: If pantograph failed, doing this means we mess up teh file state and replay gets broken..
# Similar for keyboard interrupts and all in my opinion.
# Only place we do want to do run the shutdown hooks is for token limit exceeded and all.
_should_run_hooks : bool = True
_shutdown_reason: Optional[str] = None
_shutdown_hook_scopes: list[list[Callable[[], None]]] = []


class ShutdownHookMode(Enum):
    PUSH = "push"
    CLEAR_AND_PUSH = "clear_and_push"


def request_shutdown(reason: str = "User requested shutdown", run_hooks: bool = True) -> None:
    """Request graceful shutdown of the workflow.

    The workflow should check is_shutdown_requested() between steps
    and exit cleanly when True.
    """
    global _shutdown_reason
    global _should_run_hooks
    _shutdown_reason = reason
    _should_run_hooks = run_hooks
    _shutdown_requested.set()
    logger.info(f"Shutdown requested: {reason}")


def is_shutdown_requested() -> bool:
    """Check if shutdown has been requested.

    Call this between steps to allow graceful exit.
    """
    return _shutdown_requested.is_set()


def get_shutdown_reason() -> Optional[str]:
    """Get the reason for shutdown request."""
    return _shutdown_reason


def _normalize_hooks(
    hooks: Callable[[], None] | list[Callable[[], None]],
) -> list[Callable[[], None]]:
    if callable(hooks):
        return [hooks]
    return list(hooks)


def set_shutdown_hooks(hooks: list[Callable[[], None]]) -> None:
    """Replace the currently registered shutdown hooks with one scope."""
    global _shutdown_hook_scopes
    _shutdown_hook_scopes = [list(hooks)] if hooks else []


def push_shutdown_hooks(
    hooks: Callable[[], None] | list[Callable[[], None]],
) -> None:
    """Push a nested shutdown-hook scope onto the stack."""
    normalized = _normalize_hooks(hooks)
    if normalized:
        _shutdown_hook_scopes.append(normalized)


def pop_shutdown_hooks() -> None:
    """Pop the most recently pushed shutdown-hook scope."""
    if _shutdown_hook_scopes:
        _shutdown_hook_scopes.pop()


def clear_shutdown_hooks() -> None:
    """Clear all currently registered shutdown hooks."""
    global _shutdown_hook_scopes
    _shutdown_hook_scopes = []


@contextmanager
def shutdown_hook(
    mode: ShutdownHookMode,
    hooks: Callable[[], None] | list[Callable[[], None]],
):
    """Scope shutdown hooks with automatic restoration.

    Modes:
    - ``push``: push hooks onto the current stack for the duration of the scope.
    - ``clear_and_push``: save the current stack, clear it, push the given hooks,
      and restore the previous stack when the scope exits normally.
    """
    normalized = _normalize_hooks(hooks)
    if mode is ShutdownHookMode.PUSH:
        push_shutdown_hooks(normalized)
        try:
            yield
        finally:
            pop_shutdown_hooks()
        return

    if mode is ShutdownHookMode.CLEAR_AND_PUSH:
        global _shutdown_hook_scopes
        previous = [list(scope) for scope in _shutdown_hook_scopes]
        _shutdown_hook_scopes = []
        push_shutdown_hooks(normalized)
        try:
            yield
        finally:
            _shutdown_hook_scopes = previous
        return

    raise ValueError(f"Unsupported shutdown hook mode: {mode}")


def clear_shutdown() -> None:
    """Clear shutdown state (for testing or restart)."""
    global _shutdown_reason
    _shutdown_requested.clear()
    _shutdown_reason = None
    clear_shutdown_hooks()


def shutdown_boundary(context: str) -> Callable:
    """Decorator that checks for graceful shutdown before entering a step.

    Intended usage is directly above @DBOS.step() so the shutdown check runs
    before the DBOS-managed step starts executing.
    """
    def decorator(func: Callable) -> Callable:
        if asyncio.iscoroutinefunction(func):
            @wraps(func)
            async def async_wrapper(*args, **kwargs):
                handle_shutdown_if_requested(context)
                return await func(*args, **kwargs)
            return async_wrapper

        @wraps(func)
        def sync_wrapper(*args, **kwargs):
            handle_shutdown_if_requested(context)
            return func(*args, **kwargs)
        return sync_wrapper

    return decorator


class ShutdownRequested(Exception):
    """Exception raised when shutdown is requested.

    This is a clean exit, not an error. DBOS should treat this
    as a pause point for later resumption.
    """
    def __init__(self, reason: str = "Shutdown requested"):
        self.reason = reason
        super().__init__(reason)


def _run_shutdown_hooks() -> None:
    """Run registered shutdown hooks in LIFO order."""
    if not _should_run_hooks:
        return
    flattened = [hook for scope in _shutdown_hook_scopes for hook in scope]
    total = len(flattened)
    index = 0
    for scope in reversed(_shutdown_hook_scopes):
        for hook in reversed(scope):
            index += 1
            try:
                logger.info(f"Running shutdown hook {index}/{total}")
                hook()
            except Exception as e:
                logger.warning(f"Shutdown hook {index} failed: {e}", exc_info=e)


def handle_shutdown_if_requested(context: str = "") -> None:
    """Check for shutdown request and handle it gracefully.

    Call this between DBOS steps. If shutdown was requested:
    1. Runs registered shutdown hooks
    2. Closes LSP connections
    3. Saves token usage to session
    4. Saves TUI state
    5. Exits the process with code 130 (SIGINT convention)

    This leaves the DBOS workflow in PENDING state, allowing it to be
    resumed later. On resume, completed steps return cached results.

    Args:
        context: Description of where we're pausing (e.g., "shallow solve iteration 3")
    """
    if not is_shutdown_requested():
        return

    import os

    reason = get_shutdown_reason() or "User requested shutdown"
    logger.info(f"Shutdown requested at: {context}")
    logger.info(f"Reason: {reason}")
    logger.info("Cleaning up and exiting to leave workflow PENDING for resume...")

    # Run registered shutdown hooks before generic cleanup/snapshots.
    _run_shutdown_hooks()

    # Close MCP connections
    try:
        import asyncio
        from tools.mcp_tools import cleanup_mcp
        try:
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            coro = cleanup_mcp()
            loop.run_until_complete(coro)
            loop.close()
            logger.info("MCP connections cleaned up")
        except Exception as e:
            # If run_until_complete failed, the coroutine was never awaited.
            # Close it explicitly to suppress RuntimeWarning.
            try:
                coro.close()
            except Exception:
                pass
            logger.info(f"MCP cleanup: {e}")
    except ImportError:
        pass  # MCP tools not available

    # Save token usage
    try:
        from utils.token_tracker import get_token_tracker
        tracker = get_token_tracker()
        tracker._save_to_session()
        logger.info("Token usage saved")
    except Exception as e:
        logger.warning(f"Failed to save token usage: {e}")

    # Save TUI state if available
    try:
        from tui.log_handler import get_tui_log_handler
        from tui.snapshot import TUISnapshot
        from tui.app import build_params_dict
        from args import get_args
        from config.constants import SESSIONS_DIR
        from pathlib import Path

        args = get_args()
        if args.session_name:
            session_dir = Path(SESSIONS_DIR) / args.session_name
            handler = get_tui_log_handler()
            tracker = get_token_tracker()
            params = build_params_dict()

            snapshot = TUISnapshot.from_tracker(params, tracker, handler.get_logs())
            snapshot.save(session_dir)
            logger.info(f"TUI state saved to {session_dir}")
    except Exception as e:
        logger.warning(f"Failed to save TUI state: {e}")

    logger.info("Exiting process - workflow will remain PENDING for resume")
    logger.info("To resume, re-run the same command with --resume")
    # Exit with 130 (128 + SIGINT signal 2) - conventional for Ctrl+C interruption
    # This leaves workflow PENDING in DBOS
    os._exit(130)
