"""File operation tools and session state management."""

import shutil
import tempfile
from pathlib import Path
from langchain_core.tools import tool

from logging_config import get_logger

logger = get_logger(__name__)

# Debug configuration - shared across all tool calls in a session
_debug_dir = None
_write_counter = 0
_allowed_output_files = []  # List of file paths that write_file is allowed to write to


def _get_debug_dir():
    """Get or create the debug directory for this session."""
    global _debug_dir
    if _debug_dir is None:
        _debug_dir = Path(tempfile.mkdtemp(prefix="lloom_debug_"))
        print(f"[DEBUG] Session debug directory: {_debug_dir}")
    return _debug_dir


def set_allowed_output_files(file_paths: list[str]):
    """Set the file paths that write_file is allowed to write to.

    Args:
        file_paths: List of absolute paths to allowed output files
    """
    global _allowed_output_files
    _allowed_output_files = [str(Path(fp).resolve()) for fp in file_paths]
    logger.info(f"Set allowed output files: {_allowed_output_files}")

    # Update TUI with current file
    if _allowed_output_files:
        from utils.token_tracker import set_current_file

        set_current_file(_allowed_output_files[0])


def clear_allowed_output_files():
    """Clear the allowed output files restriction."""
    global _allowed_output_files
    _allowed_output_files = []
    logger.info("Cleared allowed output files restriction")

    # Clear TUI file display
    from utils.token_tracker import set_current_file

    set_current_file(None)


@tool
def read_file(file_path: str) -> str:
    """Read the contents of a file.

    Args:
        file_path: Path to the file to read

    Returns:
        The contents of the file as a string
    """
    path = Path(file_path)
    if not path.exists():
        return f"Error: File not found: {file_path}"
    if not path.is_file():
        return f"Error: Not a file: {file_path}"
    try:
        logger.info(f"Reading {path}")
        return path.read_text()
    except Exception as e:
        return f"Error reading file: {str(e)}"


@tool
def list_files(directory: str, pattern: str = "*") -> str:
    """List files in a directory, optionally matching a pattern.

    Args:
        directory: Path to the directory
        pattern: Glob pattern to match files (default: "*")

    Returns:
        Newline-separated list of file paths
    """
    path = Path(directory)
    if not path.exists():
        return f"Error: Directory not found: {directory}"
    if not path.is_dir():
        return f"Error: Not a directory: {directory}"
    try:
        files = list(path.glob(pattern))
        if not files:
            return f"No files matching '{pattern}' in {directory}"
        return "\n".join(str(f) for f in sorted(files))
    except Exception as e:
        return f"Error listing files: {str(e)}"


@tool
def write_file(file_path: str, content: str) -> str:
    """Write content to a file.

    Args:
        file_path: Path to the file to write
        content: Content to write to the file

    Returns:
        Success or error message
    """
    global _write_counter, _allowed_output_files

    try:
        # Resolve the path to absolute for comparison
        path = Path(file_path).resolve()

        # Check if writing is restricted to specific files
        if _allowed_output_files:
            # Convert all allowed paths to Path objects for comparison
            allowed_paths = [Path(fp) for fp in _allowed_output_files]

            if path not in allowed_paths:
                error_msg = f"ERROR: Cannot write to {file_path}. Only allowed to write to: {_allowed_output_files}"
                logger.error(error_msg)
                return error_msg

        # Write to the actual target location
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

        # Log the full content
        logger.info(f"Wrote to {file_path} ({len(content)} chars)")
        logger.info(f"Content:\n{'=' * 80}\n{content}\n{'=' * 80}")

        # Save a debug copy with counter prefix
        debug_dir = _get_debug_dir()
        debug_filename = f"{_write_counter}_{path.name}"
        debug_path = debug_dir / debug_filename
        shutil.copy2(str(path), debug_path)

        print(f"[DEBUG] Write #{_write_counter}: {debug_path}")
        _write_counter += 1

        return f"Successfully wrote to {file_path}"
    except Exception as e:
        return f"Error writing file: {str(e)}"


@tool
def write_method(file_path: str, method_content: str) -> str:
    """Write a method implementation to the Impl section of a Lean file.

    This tool ONLY modifies the Impl section, preserving all other sections
    (Specs, TestCases, etc.) exactly as they are.

    Args:
        file_path: Path to the Lean file (must already exist with sections)
        method_content: The complete method implementation to write

    Returns:
        Success or error message
    """
    global _write_counter, _allowed_output_files

    try:
        from utils.lean.parser import LeanFile

        path = Path(file_path).resolve()

        # Check if writing is restricted to specific files
        if _allowed_output_files:
            allowed_paths = [Path(fp) for fp in _allowed_output_files]
            if path not in allowed_paths:
                error_msg = f"ERROR: Cannot write to {file_path}. Only allowed to write to: {_allowed_output_files}"
                logger.error(error_msg)
                return error_msg

        # File must exist (should be prepared before LLM call)
        if not path.exists():
            return f"ERROR: File does not exist: {file_path}. File must be prepared before calling write_method."

        # Parse the existing file
        try:
            lean_file = LeanFile.from_path(str(path))
        except ValueError as e:
            return f"ERROR: Failed to parse file: {e}"

        # Find and replace Impl section
        impl_section = lean_file.get_section("Impl")

        if impl_section is None:
            return f"ERROR: No 'Impl' section found in {file_path}"

        # Replace the Impl section content
        lean_file.add_or_replace_section("Impl", method_content)
        lean_file.reconstruct_and_write_to_file(path)

        logger.info(
            f"Wrote method to Impl section in {file_path} ({len(method_content)} chars)"
        )
        logger.info(f"Full content written to Impl section:\n{method_content}")

        # Save a debug copy
        debug_dir = _get_debug_dir()
        debug_filename = f"{_write_counter}_{path.name}"
        debug_path = debug_dir / debug_filename
        shutil.copy2(str(path), debug_path)
        _write_counter += 1

        return f"Successfully wrote method to Impl section in {file_path}"
    except Exception as e:
        return f"Error writing method: {str(e)}"


@tool
def find_string_in_file(file_path: str, search_string: str, occurrence: int = 1) -> str:
    """Find the position of a string in a file. VERY USEFUL for locating specific code positions.

    This tool is essential when you need to:
    - Find the exact position of a lemma, theorem, or definition in a Lean file
    - Get line/column coordinates to use with other Lean LSP tools (lean_goal, lean_hover_info)
    - Locate where to inspect proof goals or get hover information
    - Navigate to specific declarations or proof steps

    Common use cases:
    - Find "theorem my_theorem" to check its proof goal
    - Locate "lemma helper" to get hover info about its type
    - Find specific tactic invocations like "apply" or "induction"

    Args:
        file_path: Path to the file to search
        search_string: The exact string to find (e.g., "lemma my_helper", "theorem main_result")
        occurrence: Which occurrence to find (1 = first, 2 = second, etc.)

    Returns:
        JSON string with 1-indexed position (compatible with Lean LSP tools):
        {
            "start_line": int,    # Line where string starts (1-indexed)
            "start_col": int,     # Column where string starts (1-indexed)
            "end_line": int,      # Line where string ends (1-indexed)
            "end_col": int        # Column where string ends (1-indexed)
        }
        or error message if not found

    Note: Returns 1-indexed positions (line 1 = first line, column 1 = first character)
          These positions can be directly used with lean_goal and lean_hover_info tools.

    Example workflow:
        1. find_string_in_file("MyFile.lean", "lemma my_helper")
           -> {"start_line": 42, "start_col": 1, "end_line": 42, "end_col": 17}
        2. lean_goal("MyFile.lean", 42) -> Get proof goal at that lemma
        3. lean_hover_info("MyFile.lean", 42, 7) -> Get type info for the lemma name
    """
    from utils.file_helpers import find_string_position

    path = Path(file_path)
    if not path.exists():
        return f"Error: File not found: {file_path}"
    if not path.is_file():
        return f"Error: Not a file: {file_path}"

    try:
        content = path.read_text()
        # Use 1-indexed for Lean LSP compatibility
        position = find_string_position(
            content, search_string, zero_indexed=False, occurrence=occurrence
        )

        if position is None:
            return f"String '{search_string}' occurrence {occurrence} not found in {file_path}"

        # Return the complete position information
        return position.to_json()
    except Exception as e:
        return f"Error searching file: {str(e)}"
