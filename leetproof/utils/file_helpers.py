"""General file manipulation helpers."""

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Optional
from logging_config import get_logger

logger = get_logger(__name__)


@dataclass
class StringPosition:
    """Position of a string in file content."""
    start_line: int
    start_col: int
    end_line: int
    end_col: int

    def to_dict(self) -> dict:
        """Convert to dictionary (for JSON serialization or tool output)."""
        return {
            "start_line": self.start_line,
            "start_col": self.start_col,
            "end_line": self.end_line,
            "end_col": self.end_col
        }

    def to_json(self) -> str:
        """Convert to JSON string."""
        return json.dumps(self.to_dict())


def find_string_position(
    content: str,
    search_string: str,
    zero_indexed: bool = True,
    occurrence: int = 1
) -> Optional[StringPosition]:
    """Find the position of a string in file content.

    Args:
        content: File content to search
        search_string: String to find
        zero_indexed: If True, return 0-indexed; if False, 1-indexed
        occurrence: Which occurrence to find (1 = first, 2 = second, etc.)

    Returns:
        StringPosition object or None if not found
    """
    if occurrence < 1:
        logger.warning(f"Invalid occurrence {occurrence}, must be >= 1")
        return None

    lines = content.split('\n')
    found_count = 0

    for line_idx, line in enumerate(lines):
        col_idx = 0
        while True:
            col_idx = line.find(search_string, col_idx)
            if col_idx == -1:
                break

            found_count += 1
            if found_count == occurrence:
                # Calculate end position
                end_line_idx = line_idx
                end_col_idx = col_idx + len(search_string)

                # Handle multiline search strings
                newlines_in_search = search_string.count('\n')
                if newlines_in_search > 0:
                    remaining = search_string[search_string.rfind('\n') + 1:]
                    end_line_idx += newlines_in_search
                    end_col_idx = len(remaining)

                # Adjust for 0 or 1 indexing
                offset = 0 if zero_indexed else 1
                return StringPosition(
                    start_line=line_idx + offset,
                    start_col=col_idx + offset,
                    end_line=end_line_idx + offset,
                    end_col=end_col_idx + offset
                )

            col_idx += 1

    logger.debug(f"String '{search_string}' occurrence {occurrence} not found")
    return None


def verify_file_matches_stable_program(file_path: str, stable_program: str) -> str:
    """Verify that file content matches stable_program (last typechecked version).

    Args:
        file_path: Path to the file to verify
        stable_program: Expected stable program content

    Returns:
        The file content (same as stable_program)

    Raises:
        AssertionError: If file content doesn't match stable_program
        FileNotFoundError: If file doesn't exist
    """
    path = Path(file_path)
    if not path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")

    current_content = path.read_text()

    if stable_program:
        assert current_content.strip() == stable_program.strip(), \
            f"File content doesn't match stable_program! File has {len(current_content)} chars, stable has {len(stable_program)} chars"
        logger.info(f"Verified {file_path} matches stable_program ({len(stable_program)} chars)")
    else:
        logger.warning(f"No stable_program provided to verify {file_path} against")

    return current_content
