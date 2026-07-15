"""Unified runner that handles TUI and non-TUI modes transparently."""
import asyncio
import json
import signal
import threading
import time
from datetime import datetime
from pathlib import Path
from typing import Callable, Awaitable, Any

from args import get_args
from config.constants import SESSIONS_DIR
from logging_config import setup_logging, get_logger
from tui.app import build_params_dict
from utils.token_tracker import log_token_usage_on_exit, set_tui_app, get_token_tracker
from utils.shutdown import request_shutdown, clear_shutdown, is_shutdown_requested, ShutdownRequested
from config.timeouts import Timeouts

logger = get_logger(__name__)


def _get_session_log_file() -> str:
    """Get the log file path within the session directory."""
    try:
        args = get_args()
        session_dir = Path(SESSIONS_DIR) / args.session_name
        session_dir.mkdir(parents=True, exist_ok=True)
        return str(session_dir / "session.log")
    except Exception:
        return ".lloom/lloom-agent.log"


def run(workflow: Callable[[], Awaitable[Any]]) -> None:
    """
    Run a workflow with optional TUI.

    If TUI is enabled, displays the TUI and runs workflow in background.
    If TUI is disabled, runs workflow directly with console logging.

    Args:
        workflow: Async function that runs the actual workflow
    """
    args = get_args()
    tui_enabled = not args.no_tui

    # Setup logging with session-specific log file
    session_log_file = _get_session_log_file()
    setup_logging(level=args.log_level, log_file=session_log_file)

    if tui_enabled:
        _run_with_tui(workflow)
    else:
        _run_without_tui(workflow)


def _run_with_tui(workflow: Callable[[], Awaitable[Any]]) -> None:
    """Run workflow with TUI interface."""
    from tui.app import LLoomTUI
    from tui.log_handler import get_tui_log_handler
    from tui.snapshot import TUISnapshot

    params = build_params_dict()
    app = LLoomTUI(params=params)

    # Connect TUI to token tracker and log handler
    set_tui_app(app)
    tui_log_handler = get_tui_log_handler()
    tui_log_handler.set_app(app)

    workflow_error = None
    workflow_thread = None
    shutdown_event = threading.Event()

    # Track timing - may be adjusted if resuming
    start_time = datetime.now()
    start_timestamp = time.time()
    previous_elapsed = 0.0

    # Load previous session state if resuming
    args = get_args()
    if args.resume and args.session_name:
        session_dir = Path(SESSIONS_DIR) / args.session_name
        state_file = session_dir / "tui_state.json"
        if state_file.exists():
            try:
                prev_snapshot = TUISnapshot.load(session_dir)
                logger.info(f"Loaded previous session state from {state_file}")

                # Skip preloading previous logs on resume — they clutter the TUI
                # and the resumed workflow will generate its own fresh logs.
                # Previous logs are still saved in tui_state.json for reference.

                # Track previous elapsed time to add to current
                previous_elapsed = prev_snapshot.elapsed_seconds

                # Update TUI with previous token counts (tracker already loaded them)
                tracker = get_token_tracker()
                def update_token_display():
                    app.update_tokens(
                        tracker.total_prompt_tokens,
                        tracker.total_completion_tokens,
                        tracker.total_tokens,
                        tracker.max_input_tokens,
                        tracker.max_output_tokens,
                        tracker.max_total_tokens,
                        tracker.agent_usage,
                        tracker.total_cache_read_tokens,
                        tracker.total_cache_write_tokens,
                        tracker.total_cost,
                    )
                    app.update_llm_calls(tracker.call_count)
                app.call_later(update_token_display)

            except Exception as e:
                logger.warning(f"Failed to load previous session state: {e}")

    def run_workflow_in_thread():
        nonlocal workflow_error
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            loop.run_until_complete(workflow())
        except KeyboardInterrupt:
            logger.info("Workflow interrupted by KeyboardInterrupt")
            request_shutdown("KeyboardInterrupt", run_hooks=False)
        except ShutdownRequested as e:
            # This shouldn't happen anymore - we use handle_shutdown_if_requested()
            # which calls os._exit() directly. But just in case:
            logger.info(f"Workflow pausing: {e.reason}")
            try:
                tracker = get_token_tracker()
                tracker._save_to_session()
            except Exception:
                pass
            import os
            os._exit(130)
        except Exception as e:
            workflow_error = e
            logger.error(f"Workflow failed: {e}", exc_info=e)

            # For token/cost limit exceptions, exit TUI immediately
            from utils.token_tracker import TokenLimitExceededError, CostLimitExceededError
            if isinstance(e, (TokenLimitExceededError, CostLimitExceededError)):
                logger.info("Limit exceeded, forcing TUI exit...")
                # Force immediate TUI exit for limit exceptions
                try:
                    app.call_from_thread(app.exit)
                except Exception:
                    pass
        finally:
            # Cleanup MCP connections first
            try:
                from tools.mcp_tools import cleanup_mcp
                loop.run_until_complete(cleanup_mcp())
            except Exception:
                pass

            # Gracefully shutdown the event loop
            # NOTE: Don't aggressively cancel tasks - let them finish naturally
            # to avoid "cannot schedule new futures after shutdown" errors
            try:
                loop.run_until_complete(loop.shutdown_asyncgens())
            except Exception:
                pass
            finally:
                loop.close()
            shutdown_event.set()
            try:
                app.call_from_thread(app.exit)
            except Exception:
                pass  # App might already be dead

    def start_workflow():
        nonlocal workflow_thread
        workflow_thread = threading.Thread(target=run_workflow_in_thread, daemon=False)
        workflow_thread.start()

    # Start workflow when app is mounted
    app.call_later(start_workflow)

    try:
        app.run()
    except KeyboardInterrupt:
        logger.info("TUI interrupted by Ctrl+C")

    # Request graceful shutdown and wait for workflow to finish current step
    if workflow_thread and workflow_thread.is_alive():
        logger.info("Requesting graceful shutdown, waiting for current step to complete...")
        logger.info("Press Ctrl+C again to force quit immediately.")
        request_shutdown("TUI closed", run_hooks=False)

        # Install a handler so a second Ctrl+C force-quits immediately.
        # Saves token usage before exiting so progress isn't lost.
        def _force_quit(signum, frame):
            logger.info("Force quitting...")
            try:
                tracker = get_token_tracker()
                tracker._save_to_session()
            except Exception:
                pass
            import os
            os._exit(130)
        signal.signal(signal.SIGINT, _force_quit)

        # Give the workflow time to finish the current step gracefully
        workflow_thread.join(timeout=Timeouts.WORKFLOW_THREAD_JOIN)
        if workflow_thread.is_alive():
            logger.warning("Workflow did not finish gracefully within timeout, force quitting")
            try:
                tracker = get_token_tracker()
                tracker._save_to_session()
            except Exception:
                pass
            import os
            os._exit(130)

    # Clear shutdown state for potential future runs
    clear_shutdown()
    shutdown_event.set()

    # Clear TUI references before logging (app is no longer running)
    set_tui_app(None)
    tui_log_handler = get_tui_log_handler()
    tui_log_handler.set_app(None)

    # Log token summary to file
    tracker = get_token_tracker()
    tracker.log_summary()

    # Calculate timing (include previous elapsed time if resuming)
    end_time = datetime.now()
    elapsed_seconds = time.time() - start_timestamp + previous_elapsed

    # Save TUI state for replay
    _save_tui_state(
        params, tracker, tui_log_handler.get_logs(), workflow_error,
        start_time=start_time.isoformat(),
        end_time=end_time.isoformat(),
        elapsed_seconds=elapsed_seconds,
    )

    # Print summary to console
    _print_exit_summary(tracker, params, workflow_error, elapsed_seconds)

    # Re-raise workflow error if any
    if workflow_error:
        raise workflow_error


def _save_tui_state(
    params: dict,
    tracker,
    logs: list,
    error: Exception | None = None,
    start_time: str | None = None,
    end_time: str | None = None,
    elapsed_seconds: float = 0.0,
) -> None:
    """Save TUI state to session directory for later replay."""
    try:
        from tui.snapshot import TUISnapshot

        args = get_args()
        session_dir = Path(SESSIONS_DIR) / args.session_name

        snapshot = TUISnapshot.from_tracker(
            params, tracker, logs, error,
            start_time=start_time,
            end_time=end_time,
            elapsed_seconds=elapsed_seconds,
        )
        snapshot.save(session_dir)

    except Exception as e:
        # Don't fail if we can't save state
        print(f"Warning: Could not save TUI state: {e}")


def _print_exit_summary(tracker, params: dict, error: Exception | None = None, elapsed_seconds: float = 0.0) -> None:
    """Print a summary to console when exiting."""
    print()
    print("=" * 60)
    print("LLoom Agent - Session Complete")
    print("=" * 60)

    # Duration
    if elapsed_seconds > 0:
        hours, remainder = divmod(int(elapsed_seconds), 3600)
        minutes, secs = divmod(remainder, 60)
        if hours > 0:
            duration_str = f"{hours}h {minutes}m {secs}s"
        elif minutes > 0:
            duration_str = f"{minutes}m {secs}s"
        else:
            duration_str = f"{secs}s"
        print(f"\nDuration: {duration_str}")

    # Session info
    if params:
        print()
        print("Session Info:")
        for key, value in params.items():
            print(f"  {key}: {value}")

    # Token usage
    print()
    print("Token Usage:")
    print(f"  LLM Calls:      {tracker.call_count}")
    print(f"  Input Tokens:   {tracker.total_prompt_tokens:,}")
    print(f"  Output Tokens:  {tracker.total_completion_tokens:,}")
    print(f"  Total Tokens:   {tracker.total_tokens:,}")

    # Cost if available
    if tracker.total_cost > 0:
        print(f"  Total Cost:     ${tracker.total_cost:.4f}")

    # Per-agent breakdown
    if tracker.agent_usage:
        print()
        print("Per-Agent Breakdown:")
        for agent_name, usage in sorted(tracker.agent_usage.items()):
            calls = usage['call_count']
            inp = usage['prompt_tokens']
            out = usage['completion_tokens']
            print(f"  {agent_name} ({calls} calls): ↓{inp:,} ↑{out:,}")

    # Status
    print()
    if error:
        # Check if it's a limit exception for clearer messaging
        from utils.token_tracker import TokenLimitExceededError, CostLimitExceededError
        if isinstance(error, CostLimitExceededError):
            print(f"Status: STOPPED - Cost limit exceeded (${error.current:.4f} > ${error.limit:.2f})")
        elif isinstance(error, TokenLimitExceededError):
            print(f"Status: STOPPED - {error.limit_type.title()} token limit exceeded ({error.current:,} > {error.limit:,})")
        else:
            print(f"Status: FAILED - {error}")
    else:
        print("Status: Completed")

    print("=" * 60)
    print()


@log_token_usage_on_exit
async def _run_without_tui_async(workflow: Callable[[], Awaitable[Any]]) -> None:
    """Run workflow without TUI (with token logging on exit)."""
    params = build_params_dict()
    workflow_error = None
    try:
        await workflow()
    except Exception as e:
        workflow_error = e
        # For token/cost limit exceptions, provide clear feedback
        from utils.token_tracker import TokenLimitExceededError, CostLimitExceededError
        if isinstance(e, (TokenLimitExceededError, CostLimitExceededError)):
            logger.error(f"Limit exceeded: {e}")
        else:
            logger.error(f"Workflow failed: {e}", exc_info=e)
    finally:
        try:
            from tools.mcp_tools import cleanup_mcp
            await cleanup_mcp()
        except Exception:
            pass
        # Cleanup MCP connections
        # Log token summary to file
        tracker = get_token_tracker()
        tracker.log_summary()

        # Print summary to console
        _print_exit_summary(tracker, params, workflow_error)

        # Re-raise workflow error if any
        if workflow_error:
            raise workflow_error


def _run_without_tui(workflow: Callable[[], Awaitable[Any]]) -> None:
    """Run workflow directly without TUI."""
    asyncio.run(_run_without_tui_async(workflow))
