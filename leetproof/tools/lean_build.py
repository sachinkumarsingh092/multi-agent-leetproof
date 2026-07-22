"""Lean build tools and helper functions."""

import os
import signal
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, List
from langchain_core.tools import tool

from logging_config import get_logger
from tools.pantograph_client import PantographFactory
from utils.lean.constants import LOOM_SOLVE_SIMP_ALL
from utils.lean.goals import parse_lean_goals
from utils.lean_helpers import LakeBuildResult, LeanDiagnostic
from utils.lean.types import Goal
from utils.velvet_helpers import get_velvet_method

logger = get_logger(__name__)


@dataclass
class ProcessResult:
    """Result from subprocess execution."""
    stdout: str
    stderr: str
    returncode: int


def lean_build_file_helper(
    file_path: str,
    validate_fn: Callable | None = None,
    context_lines: int = 2,
    truncate_messages: bool = True,
    include_info_logs: bool = False,
    timeout_seconds: int | None = None,
) -> LakeBuildResult:
    """Helper function to build a Lean file and parse diagnostics.

    Args:
        file_path: Path to the Lean file
        validate_fn: Optional validation function with signature:
                     (diagnostics: List[LeanDiagnostic], return_code: int, build_output: str) -> str | None
                     Returns error message (str) if validation fails, None if ok.
                     If error is returned, it's appended to build_log and typechecks = False
        context_lines: Number of context lines to include in diagnostics (default: 2)
        truncate_messages: Whether to truncate long diagnostic messages (default: True)
        timeout_seconds: Optional timeout override in seconds. Defaults to Timeouts.LEAN_BUILD.

    Returns:
        Dictionary with:
            - typechecks (bool): Whether the build succeeded (return_code == 0 AND validate_fn passed)
            - build_log (str): Raw build output (with validation error appended if failed)
            - diagnostics (List[LeanDiagnostic]): Parsed diagnostics with context

    Examples:
        # Fail only on errors
        result = lean_build_file_helper(
            "file.lean",
            validate_fn=lambda diags, rc, out: "Has errors" if any(d.severity == "error" for d in diags) else None
        )

        # Fail if sorry is present
        result = lean_build_file_helper(
            "file.lean",
            validate_fn=lambda diags, rc, out: "Sorry not allowed" if "sorry" in out.lower() else None
        )
    """
    from utils.lean_helpers import parse_lake_build_output, _add_context_to_diagnostic

    try:
        # Lazy import to avoid circular dependency with utils.lean
        from config.timeouts import Timeouts
        build_timeout = Timeouts.LEAN_BUILD if timeout_seconds is None else timeout_seconds

        # Type-check an arbitrary source path in the Lake environment.
        process = subprocess.Popen(
            ["lake", "env", "lean", file_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )

        try:
            stdout, stderr = process.communicate(timeout=build_timeout)
            result = ProcessResult(stdout=stdout or "", stderr=stderr or "", returncode=process.returncode)
        except subprocess.TimeoutExpired:
            # Kill the entire process group (lake + any child processes it spawned)
            logger.error(f"Build timed out after {build_timeout}s, killing process group...")
            try:
                os.killpg(os.getpgid(process.pid), signal.SIGTERM)
                process.wait(timeout=5)  # Give it a chance to terminate gracefully
            except (ProcessLookupError, subprocess.TimeoutExpired):
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                except ProcessLookupError:
                    pass
            process.wait()  # Final cleanup
            return LakeBuildResult(
                typechecks=False,
                diagnostics=[
                    LeanDiagnostic(
                        severity="error",
                        message=f"Lean build timed out after {build_timeout}s",
                        line=0,
                        column=0,
                    )
                ],
            )

        # Combine stdout and stderr for parsing
        build_output = ""
        if result.stdout:
            build_output += result.stdout
        if result.stderr:
            build_output += "\n" + result.stderr

        if not build_output:
            build_output = (
                "Build successful"
                if result.returncode == 0
                else "Build failed with no output"
            )

        logger.debug(f"Full lake build output for {file_path}:\n{build_output}")

        # Parse diagnostics from build output
        raw_diagnostics = parse_lake_build_output(
            build_output, file_path, truncate_messages=truncate_messages
        )

        if not include_info_logs:
            # Filter out info diagnostics (only keep warnings and errors)
            raw_diagnostics = [d for d in raw_diagnostics if d["severity"] != "info"]

        # Add context to diagnostics if we have any
        diagnostics_with_context = []
        if raw_diagnostics:
            try:
                file_content = Path(file_path).read_text()
                file_lines = file_content.split("\n")

                for diag_dict in raw_diagnostics:
                    diag = _add_context_to_diagnostic(
                        diag_dict, file_lines, context_lines
                    )
                    diagnostics_with_context.append(diag)

                logger.info(
                    f"Parsed {len(diagnostics_with_context)} diagnostic(s) from build output"
                )
            except Exception as e:
                logger.warning(f"Could not add context to diagnostics: {e}")
                # Fall back to diagnostics without context
                diagnostics_with_context = [
                    LeanDiagnostic(
                        severity=d["severity"],
                        message=d["message"],
                        line=d["line"],
                        column=d["column"],
                    )
                    for d in raw_diagnostics
                ]

        # Run custom validation if provided
        validation_error = None
        if validate_fn is not None:
            validation_error = validate_fn(
                diagnostics_with_context, result.returncode, build_output
            )

        # Determine if build passed
        # Build passes if: return_code == 0 AND no validation error
        typechecks = result.returncode == 0 and validation_error is None

        # Assert invariant: returncode == 0 should mean no error diagnostics
        has_error_diagnostics = any(
            d.severity == "error" for d in diagnostics_with_context
        )
        if result.returncode == 0 and has_error_diagnostics:
            logger.warning(
                "Invariant violation: returncode == 0 but error diagnostics found"
            )
        if result.returncode != 0 and not has_error_diagnostics:
            logger.warning(
                f"Invariant violation: returncode == {result.returncode} but no error diagnostics found"
            )

        if validation_error:
            logger.info(f"⚠ Build validation failed: {validation_error}")
            build_output += f"\n\nValidation failed: {validation_error}"

        separator = "=" * 60
        build_lines = build_output.splitlines()
        above_10 = "\n".join(build_lines[:10])
        below_10 = "\n".join(build_lines[-10:])
        logger.info(
            f"Build output:\n{separator}\n*First 10 lines:*\n {above_10}\n\n *Last 10 lines:*\n {below_10}\n {separator}"
        )

        return LakeBuildResult(
            typechecks=typechecks,
            diagnostics=diagnostics_with_context,
            build_log=build_output,
        )

    except Exception as e:
        logger.error(f"Build error: {str(e)}")
        return LakeBuildResult(
            typechecks=False,
            diagnostics=[
                LeanDiagnostic(
                    severity="error", message=f"Build error: {str(e)}", line=0, column=0
                )
            ],
        )


@tool
def lean_build_file(file_path: str, ignore_sorry: bool = False) -> str:
    """Run build on the lean file

    Args:
        file_path: Path to the file to build
        ignore_sorry: If True, allow build to succeed even if 'sorry' is present (default: False)

    Returns:
        BUILD message for the lean file
    """

    # Default validation: fail if sorry is present (unless ignore_sorry=True)
    def default_validate(diagnostics, return_code, build_output):
        if not ignore_sorry and "sorry" in build_output.lower():
            return "SORRY FOUND, SORRY IS NOT ALLOWED"
        return None

    return lean_build_file_helper(
        file_path=file_path, validate_fn=default_validate
    ).build_log


@tool
def get_lean_diagnostics(file_path: str) -> str:
    """Get pretty-printed compilation diagnostics (errors and warnings) for a Lean file.

    This tool builds the file and returns only the error and warning messages
    in a clean, readable format. Use this to check for compilation issues.

    Args:
        file_path: Path to the Lean file to check

    Returns:
        Pretty-printed diagnostics showing errors and warnings, or success message
    """
    result = lean_build_file_helper(file_path)

    # Filter to only errors and warnings
    errors_and_warnings = [
        d for d in result.diagnostics if d.severity in ["error", "warning"]
    ]

    if not errors_and_warnings:
        return "✓ No errors or warnings found. File compiles successfully."

    # Pretty print using the pp() method
    output_lines = []
    error_count = sum(1 for d in errors_and_warnings if d.severity == "error")
    warning_count = sum(1 for d in errors_and_warnings if d.severity == "warning")

    output_lines.append(
        f"Found {error_count} error(s) and {warning_count} warning(s):\n"
    )

    for diagnostic in errors_and_warnings:
        output_lines.append(diagnostic.pp())
        output_lines.append("")  # Blank line between diagnostics

    return "\n".join(output_lines)


def _build_velvet_proof_probe(
    method_snippet: str,
    termination: str,
    choice: str,
    loom_solve_tactic: str,
) -> str:
    """Build a temporary Velvet snippet that runs `prove_correct` on a method."""
    method_name = get_velvet_method(method_snippet).name
    return (
        f'set_option loom.semantics.termination "{termination}"\n'
        f'set_option loom.semantics.choice "{choice}"\n\n'
        f"{method_snippet}\n\n"
        f"prove_correct {method_name} by\n"
        f"  {loom_solve_tactic}\n"
    )


async def get_remaining_vcs_for_velvet_method(
    method_snippet: str,
    termination: str = "total",
    choice: str = "demonic",
    loom_solve_tactic: str = LOOM_SOLVE_SIMP_ALL,
    include_info_logs: bool = True,
) -> tuple[list[Goal], LakeBuildResult]:
    """Get remaining Velvet verification conditions in the current problem context.

    Assumptions:
    - The current problem context is available.
    - The relevant Specs section is already available in that context.

    Returns:
        A pair of `(goals, build_result)`.

    Raises:
        RuntimeError: If the context is unavailable, the probe times out, or the
            result contains diagnostics but no parseable remaining goals.
    """
    try:
        client = PantographFactory.get_default_instance()
    except KeyError as e:
        raise RuntimeError(
            "Velvet VC probe is not available in the current context."
        ) from e

    probe = _build_velvet_proof_probe(
        method_snippet,
        termination=termination,
        choice=choice,
        loom_solve_tactic=loom_solve_tactic,
    )
    build_result = await client.check_build(probe, include_info_logs=include_info_logs)
    diagnostic_text = build_result.as_string()

    if "build timed out" in diagnostic_text.lower():
        raise RuntimeError(diagnostic_text.strip())

    goals = parse_lean_goals(diagnostic_text)
    if diagnostic_text.strip() and not goals and not build_result.typechecks:
        raise RuntimeError(
            "Velvet VC probe failed: Lean returned diagnostics, "
            "but no parseable goals were produced.\n"
            f"Raw diagnostic:\n{diagnostic_text.strip()}"
        )

    return goals, build_result


def _format_remaining_vcs(goals: list[Goal]) -> str:
    """Format remaining VCs as sorried theorem blocks."""
    return "\n\n".join(goal.as_sorried() for goal in goals)


@tool
async def get_remaining_vcs_for_velvet_method_tool(
    method_snippet: str,
    termination: str = "total",
    choice: str = "demonic",
    include_info_logs: bool = True,
) -> str:
    """Get remaining Velvet verification conditions for a method snippet."""
    goals, _ = await get_remaining_vcs_for_velvet_method(
        method_snippet=method_snippet,
        termination=termination,
        choice=choice,
        include_info_logs=include_info_logs,
    )
    return _format_remaining_vcs(goals)


@tool
async def check_velvet_method(
    method_snippet: str,
    termination: str = "total",
    choice: str = "demonic",
    include_info_logs: bool = False,
) -> str:
    """Check a Velvet method snippet in the current problem context.

    Assumptions:
    - The current problem context is available.
    - The relevant Specs section is already available in that context.

    This tool prepends the Velvet semantics options before checking the snippet.

    Args:
        method_snippet: Velvet method snippet to check in the current problem context
        termination: Value for `loom.semantics.termination` (typically `"total"`)
        choice: Value for `loom.semantics.choice` (typically `"demonic"`)
        include_info_logs: Whether to include info diagnostics

    Returns:
        Pretty-printed diagnostics or a success message
    """
    try:
        client = PantographFactory.get_default_instance()
    except KeyError:
        return "This method-check tool is not available in the current context."

    lean_code = (
        f'set_option loom.semantics.termination "{termination}"\n'
        f'set_option loom.semantics.choice "{choice}"\n\n'
        f"{method_snippet}"
    )

    result = await client.check_build(lean_code, include_info_logs=include_info_logs)
    diagnostics = result.diagnostics

    if not diagnostics:
        return "✓ No errors or warnings found. Method compiles successfully."

    error_count = sum(1 for d in diagnostics if d.severity == "error")
    warning_count = sum(1 for d in diagnostics if d.severity == "warning")
    info_count = sum(1 for d in diagnostics if d.severity == "info")

    counts = [f"{error_count} error(s)", f"{warning_count} warning(s)"]
    if include_info_logs:
        counts.append(f"{info_count} info message(s)")

    output_lines = [f"Found {', '.join(counts)}:\n"]
    for diagnostic in diagnostics:
        output_lines.append(diagnostic.pp())
        output_lines.append("")
    return "\n".join(output_lines)


@tool
async def lean_diagnostics_messages(file_path: str, severity: str = "error") -> str:
    """Get pretty-printed Lean LSP diagnostics for a file, filtered by severity.

    This tool uses the Lean LSP to get diagnostics and returns them in a clean,
    pretty-printed format with context lines. Unlike lean_build_file, this uses
    the LSP directly without running a full build.

    Args:
        file_path: Path to the Lean file to check
        severity: Filter diagnostics by severity level. Options:
                 - "error": Only errors (default)
                 - "warning": Only warnings
                 - "info": Only info messages
                 - "all": All diagnostics

    Returns:
        Pretty-printed diagnostics with context, or success message if no matches found
    """
    from utils.lean.build import get_diagnostics

    # Validate severity input
    valid_severities = ["error", "warning", "info", "all"]
    if severity not in valid_severities:
        return f"Invalid severity '{severity}'. Must be one of: {', '.join(valid_severities)}"

    try:
        # Get all diagnostics from LSP
        diagnostics = await get_diagnostics(file_path, context_lines=3)

        if not diagnostics:
            return "✓ No diagnostics found."

        # Filter by severity
        if severity != "all":
            filtered = [d for d in diagnostics if d.severity == severity]
        else:
            filtered = diagnostics

        if not filtered:
            return f"✓ No {severity} diagnostics found."

        # Pretty print using the pp() method
        output_lines = []
        severity_counts = {}
        for sev in ["error", "warning", "info"]:
            count = sum(1 for d in filtered if d.severity == sev)
            if count > 0:
                severity_counts[sev] = count

        count_str = ", ".join(
            f"{count} {sev}(s)" for sev, count in severity_counts.items()
        )
        output_lines.append(f"Found {count_str}:\n")

        for diagnostic in filtered:
            output_lines.append(diagnostic.pp())
            output_lines.append("")  # Blank line between diagnostics

        return "\n".join(output_lines)

    except Exception as e:
        return f"Error retrieving diagnostics: {str(e)}"
