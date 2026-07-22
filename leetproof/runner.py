"""Headless workflow runner used by worker CLI entry points."""

import asyncio
import os
import signal
from pathlib import Path
from typing import Any, Awaitable, Callable

from args import get_args
from config.constants import SESSIONS_DIR
from logging_config import get_logger, setup_logging
from utils.shutdown import (
    clear_shutdown,
    handle_shutdown_if_requested,
    is_shutdown_requested,
    request_shutdown,
)
from utils.token_tracker import get_token_tracker

logger = get_logger(__name__)


def _session_log_file() -> str:
    args = get_args()
    session_name = getattr(args, "session_name", None)
    if not session_name:
        return str(Path(SESSIONS_DIR) / "worker.log")
    session_dir = Path(SESSIONS_DIR) / session_name
    session_dir.mkdir(parents=True, exist_ok=True)
    return str(session_dir / "session.log")


async def _run(workflow: Callable[[], Awaitable[Any]]) -> Any:
    try:
        result = await workflow()
        handle_shutdown_if_requested("workflow completed")
        return result
    except Exception:
        handle_shutdown_if_requested("workflow stopped")
        raise
    finally:
        try:
            from tools.mcp_tools import cleanup_mcp

            await cleanup_mcp()
        finally:
            get_token_tracker().log_summary()


def _install_signal_handlers() -> dict[signal.Signals, Any]:
    previous_handlers: dict[signal.Signals, Any] = {}

    def handle_signal(signum: int, _frame: Any) -> None:
        signal_name = signal.Signals(signum).name
        if is_shutdown_requested():
            logger.warning("Second %s received; forcing worker exit", signal_name)
            try:
                get_token_tracker()._save_to_session()
            finally:
                os._exit(128 + signum)

        request_shutdown(signal_name, run_hooks=False)
        logger.warning(
            "%s received; waiting for the current durable step to finish. "
            "Send the signal again to force exit.",
            signal_name,
        )

    for handled_signal in (signal.SIGINT, signal.SIGTERM):
        previous_handlers[handled_signal] = signal.getsignal(handled_signal)
        signal.signal(handled_signal, handle_signal)
    return previous_handlers


def run(workflow: Callable[[], Awaitable[Any]]) -> Any:
    """Run an async workflow with session logging and cleanup."""
    args = get_args()
    setup_logging(
        level=getattr(args, "log_level", "INFO"),
        log_file=_session_log_file(),
        tui_mode=False,
    )
    clear_shutdown()
    previous_handlers = _install_signal_handlers()
    try:
        return asyncio.run(_run(workflow))
    finally:
        for handled_signal, previous_handler in previous_handlers.items():
            signal.signal(handled_signal, previous_handler)
