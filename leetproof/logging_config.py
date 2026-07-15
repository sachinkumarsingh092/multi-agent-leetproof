import logging
import sys
import json
from typing import Any

# ANSI color codes
COLORS = {
    "DEBUG": "\033[36m",  # Cyan
    "INFO": "\033[32m",  # Green
    "WARNING": "\033[33m",  # Yellow
    "ERROR": "\033[31m",  # Red
    "CRITICAL": "\033[35m",  # Magenta
    "RESET": "\033[0m",
}


class ColoredFormatter(logging.Formatter):
    """Custom formatter with colors for terminal output.

    Note: This formatter embeds ANSI color codes. When logging to files,
    view with `less -R` or `cat` in a terminal to see colors.
    """

    def format(self, record):
        # Create a copy to avoid mutating the original record (prevents double-coloring
        # when multiple handlers process the same record)
        record = logging.makeLogRecord(record.__dict__)

        # Add color based on level
        color = COLORS.get(record.levelname, COLORS["RESET"])
        reset = COLORS["RESET"]

        # Format the message
        record.levelname = f"{color}{record.levelname}{reset}"
        record.name = f"\033[1m{record.name}{reset}"  # Bold name

        # Get the formatted message
        formatted = super().format(record)

        # Handle multi-line messages with proper indentation
        if "\n" in formatted:
            lines = formatted.split("\n")
            # First line is the log header + first message line
            result = lines[0]
            # Indent subsequent lines for readability
            indent = " " * 4  # 4 spaces for indentation
            for line in lines[1:]:
                result += "\n" + indent + line
            return result

        return formatted


def _is_tui_enabled() -> bool:
    """Check if TUI mode is enabled from args (default: True unless --no-tui)."""
    try:
        from args import get_args

        args = get_args()
        return not getattr(args, "no_tui", False)
    except Exception:
        return False


def setup_logging(
    level: str = "INFO",
    log_file: str = "",
    tui_mode: bool | None = None,
) -> None:
    """
    Configure logging for the application.

    Args:
        level: Logging level for console/TUI (DEBUG, INFO, WARNING, ERROR, CRITICAL)
        log_file: Optional path to log file. If non-empty, file logging is enabled at DEBUG level.
        tui_mode: If True, skip console handler (TUI will handle display). If None, auto-detect from args.
    """
    # Auto-detect TUI mode from args if not explicitly provided
    if tui_mode is None:
        tui_mode = _is_tui_enabled()

    # Create root logger
    root_logger = logging.getLogger()
    root_logger.setLevel(
        logging.DEBUG
    )  # Set to DEBUG so file handler can capture everything

    # Remove existing handlers
    root_logger.handlers.clear()

    # Only add console handler if NOT in TUI mode
    if not tui_mode:
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(getattr(logging, level.upper()))

        # Create formatter
        formatter = ColoredFormatter(
            fmt="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
            datefmt="%H:%M:%S",
        )
        console_handler.setFormatter(formatter)

        # Add handler to root logger
        root_logger.addHandler(console_handler)

    # Add file handler if log_file provided
    if log_file:
        try:
            from pathlib import Path
            log_path = Path(log_file)
            log_path.parent.mkdir(parents=True, exist_ok=True)
            file_handler = logging.FileHandler(log_file, mode="a", encoding="utf-8")
            file_handler.setLevel(logging.DEBUG)
            file_formatter = ColoredFormatter(
                fmt="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
                datefmt="%Y-%m-%d %H:%M:%S",
            )
            file_handler.setFormatter(file_formatter)
            root_logger.addHandler(file_handler)
        except Exception as e:
            print(f"Warning: Could not setup file logging: {e}", file=sys.stderr)

    # If TUI mode, add the TUI log handler
    if tui_mode:
        try:
            from tui.log_handler import get_tui_log_handler

            tui_handler = get_tui_log_handler()
            tui_handler.setLevel(getattr(logging, level.upper()))
            root_logger.addHandler(tui_handler)
        except ImportError:
            # TUI module not available, fall back to console
            if not any(
                isinstance(h, logging.StreamHandler) for h in root_logger.handlers
            ):
                console_handler = logging.StreamHandler(sys.stdout)
                console_handler.setLevel(getattr(logging, level.upper()))
                formatter = ColoredFormatter(
                    fmt="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
                    datefmt="%H:%M:%S",
                )
                console_handler.setFormatter(formatter)
                root_logger.addHandler(console_handler)


def get_logger(name: str) -> logging.Logger:
    """
    Get a logger with the given name.

    Args:
        name: Logger name (usually __name__)

    Returns:
        Configured logger instance
    """
    return logging.getLogger(name)


def log_with_truncation(
    logger: logging.Logger,
    level: int,
    message: str,
    console_max_length: int = 1000,
    file_max_length: int = 50000,
) -> None:
    """
    Log a message with truncation for console output while preserving full message in file.

    Args:
        logger: Logger instance to use
        level: Logging level (e.g., logging.INFO, logging.ERROR)
        message: Message to log
        console_max_length: Maximum characters to show in console (default: 1000)
        file_max_length: Maximum characters to log to file (default: 50000)
    """
    if len(message) <= console_max_length:
        logger.log(level, message)
    else:
        # Truncate for display
        truncated = (
            message[:console_max_length]
            + f"\n... [truncated, {len(message)} total chars]"
        )
        logger.log(level, truncated)


def pretty_dict(
    obj: Any, indent: int = 2, max_depth: int = 10, _current_depth: int = 0
) -> str:
    """
    Format a Python object (dict, list, etc.) as a pretty-printed string for logging.

    Args:
        obj: Object to format (dict, list, or any Python object)
        indent: Number of spaces for indentation (default: 2)
        max_depth: Maximum nesting depth to display (default: 10)
        _current_depth: Internal parameter for tracking recursion depth

    Returns:
        Pretty-printed string representation

    Examples:
        >>> logger.info(f"Response: {pretty_dict(response_dict)}")
        >>> logger.debug(f"State:\n{pretty_dict(state, indent=4)}")
    """
    from pprint import pformat

    try:
        # Use pprint for nice formatting
        return pformat(
            obj,
            indent=indent,
            width=100,
            depth=max_depth,
            sort_dicts=True,
            compact=False,
        )
    except Exception as e:
        # Fallback to simple string representation
        return f"<Failed to format {type(obj).__name__}>: {str(e)}"
