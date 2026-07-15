"""Entry point for submitting Lean files to Aristotle and checking job status."""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

from logging_config import get_logger

logger = get_logger(__name__)

JOBS_FILE_NAME = "aristotle_jobs.json"
LLOOM_DIR = ".lloom"
TERMINAL_FAILURE_STATUSES = {"FAILED", "CANCELED", "UNKNOWN"}
DOWNLOADABLE_RESULT_STATUSES = {"COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET"}


def _jobs_file(project_dir: Path) -> Path:
    jobs_dir = project_dir / LLOOM_DIR
    jobs_dir.mkdir(parents=True, exist_ok=True)
    return jobs_dir / JOBS_FILE_NAME


def _load_jobs(jobs_file: Path) -> list[dict]:
    if jobs_file.exists():
        return json.loads(jobs_file.read_text())
    return []


def _save_jobs(jobs_file: Path, jobs: list[dict]) -> None:
    jobs_file.write_text(json.dumps(jobs, indent=2) + "\n")


def _output_path(input_file: Path) -> Path:
    """<stem>AristotleProof<suffix> beside the original file."""
    return input_file.with_name(f"{input_file.stem}AristotleProof{input_file.suffix}")


def _status_name(status: object) -> str:
    if hasattr(status, "name"):
        return str(getattr(status, "name"))
    if hasattr(status, "value"):
        return str(getattr(status, "value"))
    return str(status)


# ---------------------------------------------------------------------------
# submit
# ---------------------------------------------------------------------------

async def _run_submit(
    input_file: Path,
    project_dir: Path,
    mode: str,
    target_section: str,
) -> None:
    from utils.aristotle_helpers import (
        extract_sorries_after_loom_solve_and_submit_to_aristotle,
        extract_sorries_and_submit_to_aristotle,
    )

    output_path = _output_path(input_file)
    if mode == "loom-sorries":
        project_id, output_path = await extract_sorries_after_loom_solve_and_submit_to_aristotle(
            input_file
        )
    else:
        project_id, output_path = await extract_sorries_and_submit_to_aristotle(
            input_file,
            target_section=target_section,
        )

    jobs_file = _jobs_file(project_dir)
    jobs = _load_jobs(jobs_file)
    jobs.append({
        "input_file": str(input_file),
        "project_id": project_id,
        "status": "pending",
        "submitted_at": datetime.now(timezone.utc).isoformat(),
        "output_file": str( output_path ),
    })
    _save_jobs(jobs_file, jobs)

    print(f"Submitted. Project ID: {project_id}, Output will be written to {str(output_path)} when it's ready and you do aristotle-check")
    print(f"Jobs tracked in: {jobs_file}")


def run_submit():
    parser = argparse.ArgumentParser(
        prog="lloom-agent aristotle-submit",
        description="Strip sorry goals from a Lean file and submit to Aristotle.",
    )
    parser.add_argument(
        "--project",
        type=str,
        required=True,
        help="Lean project directory (containing lakefile.lean)",
    )
    parser.add_argument("file", type=str, help="Path to the Lean source file")
    parser.add_argument(
        "--mode",
        choices=["sorries", "loom-sorries"],
        default="sorries",
        help=(
            "Extraction mode: 'sorries' extracts plain sorry goals (default); "
            "'loom-sorries' extracts goals after loom_solve."
        ),
    )
    parser.add_argument(
        "--section",
        default="Proof",
        help="Target section name to extract from (default: Proof)",
    )
    args = parser.parse_args(sys.argv[1:])

    project_dir = Path(args.project)
    if not project_dir.is_dir():
        print(f"Error: --project directory does not exist: {project_dir}", file=sys.stderr)
        sys.exit(1)
    os.chdir(project_dir)

    input_file = Path(args.file)
    if not input_file.exists():
        print(f"Error: file not found: {input_file}", file=sys.stderr)
        sys.exit(1)

    asyncio.run(_run_submit(input_file, project_dir, args.mode, args.section))


# ---------------------------------------------------------------------------
# check-status
# ---------------------------------------------------------------------------

async def _run_check(jobs_file: Path) -> None:
    from aristotlelib import ProjectStatus

    from utils.aristotle_helpers import get_submission, get_submission_status

    jobs = _load_jobs(jobs_file)
    if not jobs:
        print("No jobs found.")
        return

    changed = False
    project_dir = jobs_file.parent.parent if jobs_file.parent.name == LLOOM_DIR else jobs_file.parent
    for job in jobs:
        if job.get("status") != "pending":
            continue

        project_id = job["project_id"]
        try:
            status = await get_submission_status(project_id)
        except Exception as exc:
            logger.warning("Could not fetch status for %s: %s", project_id, exc)
            print(f"  {project_id}: ERROR ({exc})")
            continue

        status_name = _status_name(status)
        if job.get("api_status") != status_name:
            job["api_status"] = status_name
            changed = True

        if status_name in DOWNLOADABLE_RESULT_STATUSES:
            output_path = Path(job["output_file"])
            if not output_path.is_absolute():
                output_path = project_dir / output_path
            try:
                saved = await get_submission(
                    project_id,
                    path=output_path,
                    project_root=project_dir,
                )
                if saved:
                    job["status"] = "done"
                    job["completed_at"] = datetime.now(timezone.utc).isoformat()
                    changed = True
                    print(f"  {project_id}: {status_name.lower()} -> {saved}")
            except Exception as exc:
                logger.warning("Could not download solution for %s: %s", project_id, exc)
                print(f"  {project_id}: {status_name.lower()} but download failed: {exc}")
        elif status_name in TERMINAL_FAILURE_STATUSES:
            job["status"] = "failed"
            job["completed_at"] = datetime.now(timezone.utc).isoformat()
            changed = True
            print(f"  {project_id}: {status_name.lower()} (terminal)")
        else:
            print(f"  {project_id}: {status_name} (still pending)")

    if changed:
        _save_jobs(jobs_file, jobs)
        print(f"\nJobs file updated: {jobs_file}")
    else:
        print("No jobs completed.")


def run_check():
    parser = argparse.ArgumentParser(
        prog="lloom-agent aristotle-check",
        description="Check pending Aristotle submissions and download completed solutions.",
    )
    parser.add_argument(
        "--project",
        type=str,
        required=True,
        help="Lean project directory (containing lakefile.lean)",
    )
    args = parser.parse_args(sys.argv[1:])

    project_dir = Path(os.path.abspath(args.project))
    if not project_dir.is_dir():
        print(f"Error: --project directory does not exist: {project_dir}", file=sys.stderr)
        sys.exit(1)
    os.chdir(project_dir)

    jobs_file = _jobs_file(project_dir)
    if not jobs_file.exists():
        print(f"No jobs file found at: {jobs_file}", file=sys.stderr)
        sys.exit(1)

    asyncio.run(_run_check(jobs_file))


def main():
    if len(sys.argv) < 2 or sys.argv[1] in ("--help", "-h"):
        print("Usage: lloom-agent <aristotle-submit|aristotle-check> [args...]\n")
        print("  aristotle-submit   Submit a Lean file to Aristotle")
        print("  aristotle-check    Check pending submissions and download solutions")
        return

    cmd = sys.argv[1]
    if cmd == "aristotle-submit":
        run_submit()
    elif cmd == "aristotle-check":
        run_check()
    else:
        print(f"Unknown command: {cmd}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
