"""Custom logging handler that feeds logs to the TUI."""
import logging
from typing import Optional, List, TYPE_CHECKING

if TYPE_CHECKING:
    from tui.app import LLoomTUI


class TUILogHandler(logging.Handler):
    """Logging handler that writes to the TUI log panel and collects logs."""

    def __init__(self, app: Optional["LLoomTUI"] = None, level: int = logging.NOTSET):
        super().__init__(level)
        self._app: Optional["LLoomTUI"] = app
        self._logs: List[str] = []  # Collect all logs for saving
        self._max_logs: int = 50000  # Max logs to keep in memory
        self.setFormatter(logging.Formatter(
            fmt="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
            datefmt="%H:%M:%S"
        ))

    def set_app(self, app: Optional["LLoomTUI"]) -> None:
        """Set the TUI app instance."""
        self._app = app

    def get_logs(self) -> List[str]:
        """Get all collected log messages."""
        return self._logs.copy()

    def preload_logs(self, logs: List[str]) -> None:
        """Preload logs from a previous session (for resume).

        These will be displayed in the TUI and included in saved state.
        """
        self._logs = logs.copy()
        # If app is available, write all logs to display
        if self._app is not None and self._app.is_running:
            for line in logs:
                try:
                    self._app.call_from_thread(self._app.write_log, line)
                except Exception:
                    pass

    def emit(self, record: logging.LogRecord) -> None:
        """Emit a log record to the TUI and collect it."""
        try:
            msg = self.format(record)
            # Collect log for later saving
            for line in msg.split('\n'):
                self._logs.append(line)
                # Trim if too many
                if len(self._logs) > self._max_logs:
                    self._logs = self._logs[-self._max_logs:]

            # Send to TUI if available and running
            if self._app is not None and self._app.is_running:
                for line in msg.split('\n'):
                    self._app.call_from_thread(self._app.write_log, line)
        except Exception:
            # Silently ignore errors during shutdown - don't call handleError
            # which prints stack traces when the app is exiting
            pass


# Global TUI log handler instance
_tui_handler: Optional[TUILogHandler] = None


def get_tui_log_handler() -> TUILogHandler:
    """Get or create the global TUI log handler."""
    global _tui_handler
    if _tui_handler is None:
        _tui_handler = TUILogHandler()
    return _tui_handler


def setup_tui_logging(app: "LLoomTUI") -> None:
    """Add TUI log handler to root logger."""
    handler = get_tui_log_handler()
    handler.set_app(app)
    handler.setLevel(logging.DEBUG)

    root_logger = logging.getLogger()
    root_logger.addHandler(handler)


def remove_tui_logging() -> None:
    """Remove TUI log handler from root logger."""
    global _tui_handler
    if _tui_handler is not None:
        root_logger = logging.getLogger()
        root_logger.removeHandler(_tui_handler)
        _tui_handler = None
