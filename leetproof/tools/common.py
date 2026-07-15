"""Common tools for agents - re-exports for backward compatibility.

This module re-exports everything from the specialized tool modules.
New code should import directly from tools.file_ops or tools.lean_build.
"""

# File operations and session management
from tools.file_ops import (
    read_file,
    list_files,
    write_file,
    write_method,
    find_string_in_file,
    set_allowed_output_files,
    clear_allowed_output_files,
)

# Lean build tools and helpers
from tools.lean_build import (
    check_velvet_method,
    lean_build_file,
    lean_build_file_helper,
    get_lean_diagnostics,
    lean_diagnostics_messages,
)

# List of all common tools for easy import
COMMON_TOOLS = [read_file, list_files, write_file, find_string_in_file]

__all__ = [
    # File operations
    "read_file",
    "list_files",
    "write_file",
    "write_method",
    "find_string_in_file",
    "set_allowed_output_files",
    "clear_allowed_output_files",
    # Lean build
    "check_velvet_method",
    "lean_build_file",
    "lean_build_file_helper",
    "get_lean_diagnostics",
    "lean_diagnostics_messages",
    # Tool list
    "COMMON_TOOLS",
]
