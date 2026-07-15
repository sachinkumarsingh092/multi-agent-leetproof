"""Build and diagnostics utilities for Lean files."""

import json
from pathlib import Path
from typing import List, Callable

from logging_config import get_logger
from utils.lean.types import LeanDiagnostic, LakeBuildResult

logger = get_logger(__name__)


def find_project_root(file_path: str) -> str:
    """Find the Lean project root by looking for lakefile.lean or lakefile.toml.

    Args:
        file_path: Path to a file within the Lean project

    Returns:
        Path to the project root directory

    Raises:
        FileNotFoundError: If no lakefile is found in any parent directory
    """
    path = Path(file_path).resolve().parent
    while path != path.parent:
        if (path / "lakefile.lean").exists() or (path / "lakefile.toml").exists():
            return str(path)
        path = path.parent
    raise FileNotFoundError(f"Could not find lakefile.lean or lakefile.toml in parents of {file_path}")


def get_simplified_goals_after_loom_solve(file_path: str) -> str:
    """Get the proof goals remaining after loom goal-extraction cleanup runs.

    Uses lake build to get diagnostics and extracts goals from error messages.

    Args:
        file_path: Path to the Lean file using the standard loom extraction cleanup

    Returns:
        String containing the goals (extracted from build diagnostics)
    """
    from tools.lean_build import lean_build_file_helper

    build_result = lean_build_file_helper(file_path, truncate_messages=False)

    # Goals appear in error diagnostics when unsolved - expect exactly one error
    error_messages = [diag.message for diag in build_result.diagnostics if diag.severity == "error"]

    if len(error_messages) == 0:
        return ""

    if len(error_messages) != 1:
        logger.error(f"Expected exactly one error diagnostic, got {len(error_messages)}:")
        for i, msg in enumerate(error_messages):
            logger.error(f"  [{i}]: {msg}")
        raise AssertionError(f"Expected exactly one error diagnostic, got {len(error_messages)}")

    return error_messages[0]


def get_goals_after_loom_solve(file_path: str) -> str:
    """Get the proof goals remaining after loom_solve runs.

    Uses lake build to get diagnostics and extracts goals from error messages.

    Args:
        file_path: Path to the Lean file

    Returns:
        String containing the goals (extracted from build diagnostics)
    """
    from tools.lean_build import lean_build_file_helper

    build_result = lean_build_file_helper(file_path, truncate_messages=False)

    # Goals appear in error diagnostics when unsolved - expect exactly one error
    error_messages = [diag.message for diag in build_result.diagnostics if diag.severity == "error"]

    if len(error_messages) == 0:
        return ""

    if len(error_messages) != 1:
        logger.error(f"Expected exactly one error diagnostic, got {len(error_messages)}:")
        for i, msg in enumerate(error_messages):
            logger.error(f"  [{i}]: {msg}")
        raise AssertionError(f"Expected exactly one error diagnostic, got {len(error_messages)}")

    return error_messages[0]


def _extract_items_from_diagnostics(diag_dict: dict) -> List[dict]:
    """Extract items list from diagnostics response.
    
    Expects format:
    {
        "items": [
            {
                "severity": "error",
                "message": "...",
                "line": 1,
                "column": 1
            }
        ]
    }
    """
    if not isinstance(diag_dict, dict):
        raise ValueError(f"Expected diagnostics to be a dict, got {type(diag_dict)}")
    
    if "items" not in diag_dict:
        raise ValueError(f"Expected 'items' key in diagnostics dict. Available keys: {list(diag_dict.keys())}")
    
    items = diag_dict["items"]
    if not isinstance(items, list):
        raise ValueError(f"Expected diagnostics['items'] to be a list, got {type(items)}")
    
    return items


def _add_context_to_diagnostic(
    diag_dict: dict,
    file_lines: List[str],
    context_lines: int
) -> LeanDiagnostic:
    """Add context lines to a diagnostic."""
    line = diag_dict.get('line', 1)
    column = diag_dict.get('column', 1)

    line_idx = line - 1
    line_content = file_lines[line_idx] if 0 <= line_idx < len(file_lines) else ""

    ctx_before_start = max(0, line_idx - context_lines)
    ctx_before_lines = file_lines[ctx_before_start:line_idx]
    ctx_before = "\n".join(ctx_before_lines)

    ctx_after_end = min(len(file_lines), line_idx + 1 + context_lines)
    ctx_after_lines = file_lines[line_idx + 1:ctx_after_end]
    ctx_after = "\n".join(ctx_after_lines)

    return LeanDiagnostic(
        severity=diag_dict.get('severity', 'error'),
        message=diag_dict.get('message', ''),
        line=line,
        column=column,
        line_content=line_content,
        ctx_before=ctx_before,
        ctx_after=ctx_after
    )


async def get_diagnostics(
    file_path: str,
    context_lines: int = 3,
    filter_fn: Callable | None = None
) -> List[LeanDiagnostic]:
    """Get diagnostics for a Lean file with context lines.

    Args:
        file_path: Path to the Lean file
        context_lines: Number of lines to include before/after each diagnostic
        filter_fn: Optional function to filter diagnostics

    Returns:
        List of LeanDiagnostic objects with context
    """
    from tools.mcp_tools import LEAN_DIAGNOSTICS, get_lean_lsp_tool

    diag_tool = await get_lean_lsp_tool(LEAN_DIAGNOSTICS)

    if diag_tool is None:
        raise RuntimeError("lean_diagnostic_messages MCP tool not available")

    result = await diag_tool.ainvoke({"file_path": file_path})

    if isinstance(result, str):
        try:
            result = json.loads(result)
        except json.JSONDecodeError as e:
            raise ValueError(f"Failed to parse MCP tool response as JSON: {e}")

    if not isinstance(result, dict):
        raise ValueError(f"Expected MCP tool response to be a dict, got {type(result)}")

    # Extract items from the diagnostics response
    raw_diagnostics = _extract_items_from_diagnostics(result)

    if not raw_diagnostics:
        logger.info(f"No diagnostics found for {file_path}")
        return []

    logger.info(f"Found {len(raw_diagnostics)} diagnostic(s) for {file_path}")

    file_content = Path(file_path).read_text()
    file_lines = file_content.split('\n')

    diagnostics_with_context = []
    for diag_dict in raw_diagnostics:
        diag = _add_context_to_diagnostic(diag_dict, file_lines, context_lines)

        if filter_fn is None or filter_fn(diag):
            diagnostics_with_context.append(diag)

    logger.info(f"Returning {len(diagnostics_with_context)} diagnostic(s) after filtering")

    return diagnostics_with_context


def parse_lake_build_output(build_output: str, file_path: str, truncate_messages: bool = True) -> List[dict]:
    """Parse lake build output into diagnostic dictionaries.

    Args:
        build_output: Raw output from lake build command
        file_path: File path to filter diagnostics
        truncate_messages: Whether to truncate long messages (default True)

    Returns:
        List of diagnostic dicts with keys: severity, message, line, column
    """
    diagnostics = []
    lines = build_output.split('\n')
    i = 0

    while i < len(lines):
        line = lines[i]

        if line.startswith('warning: ') or line.startswith('error: ') or line.startswith('info: '):
            if line.startswith('warning: '):
                severity = 'warning'
            elif line.startswith('error: '):
                severity = 'error'
            else:
                severity = 'info'

            rest = line[len(severity) + 2:]
            parts = rest.split(':', 3)

            if len(parts) >= 4:
                diag_file = parts[0]
                try:
                    line_no = int(parts[1])
                    col_no = int(parts[2])
                    message_first = parts[3].strip()
                except ValueError:
                    i += 1
                    continue

                message_lines = [message_first] if message_first else []
                i += 1

                while i < len(lines):
                    next_line = lines[i]
                    if next_line.startswith('warning: ') or next_line.startswith('error: ') or next_line.startswith('info: '):
                        break
                    message_lines.append(next_line)
                    i += 1

                full_message = '\n'.join(message_lines).strip()
                # Truncate if enabled
                if truncate_messages:
                    from config.limits import Limits
                    if len(full_message) > Limits.MAX_DIAGNOSTIC_MESSAGE_LENGTH:
                        full_message = full_message[:Limits.MAX_DIAGNOSTIC_MESSAGE_LENGTH] + "...TRUNCATED"

                if diag_file == file_path:
                    diagnostics.append({
                        'severity': severity,
                        'message': full_message,
                        'line': line_no,
                        'column': col_no
                    })
            else:
                i += 1
        else:
            i += 1

    return diagnostics
