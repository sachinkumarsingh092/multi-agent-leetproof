"""Two-command CLI for the small multi-worker orchestration POC."""

from __future__ import annotations

import argparse
import asyncio
import importlib
import json
import sys
from pathlib import Path

from .integration import IntegrationError, integrate_modules
from .manifest import ManifestError
from .planner import PlanError, compile_plan, generate_plan
from .sandbox import DockerSandboxConfig, DockerSandboxRunner, SandboxError
from .scheduler import ScheduleError, run_job


def _provider_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--provider",
        required=True,
        choices=("openai", "anthropic", "google"),
    )
    parser.add_argument("--model", required=True)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m orchestrator.poc",
        description="Plan and run a small reviewed multi-method job",
    )
    commands = parser.add_subparsers(dest="command", required=True)

    plan = commands.add_parser("plan", help="Propose reviewable task files")
    plan.add_argument("project_specification")
    plan.add_argument("--output-directory", "-o", required=True)
    plan.add_argument("--project-id", required=True)
    _provider_arguments(plan)

    run = commands.add_parser("run", help="Run an approved plan and integrate it")
    run.add_argument("plan_file")
    run.add_argument("--image", default="leetproof-worker:1")
    run.add_argument("--max-workers", type=int, default=2)
    run.add_argument("--cpus", type=float, default=2)
    run.add_argument("--memory", default="8g")
    run.add_argument("--pids-limit", type=int, default=256)
    run.add_argument("--lean-explore-directory", type=Path)
    run.add_argument("--huggingface-cache-directory", type=Path)
    _provider_arguments(run)
    return parser


def _plan(args: argparse.Namespace) -> None:
    token_tracker = importlib.import_module("utils.token_tracker")
    token_tracker.init_token_tracker(model_name=args.model)
    plan = asyncio.run(
        generate_plan(
            args.project_specification,
            args.output_directory,
            project_id=args.project_id,
            provider=args.provider,
            model=args.model,
        )
    )
    print(
        json.dumps(
            {
                "status": "REVIEW_REQUIRED",
                "plan_file": str(plan.plan_file),
                "task_files": [str(task.input_file) for task in plan.tasks],
                "next": (
                    "Review plan.json and every task file, then run the "
                    "'run' command."
                ),
            },
            indent=2,
        )
    )


def _run(args: argparse.Namespace) -> None:
    manifest = compile_plan(args.plan_file)
    runner = DockerSandboxRunner(
        DockerSandboxConfig(
            image=args.image,
            provider=args.provider,
            model=args.model,
            cpus=args.cpus,
            memory=args.memory,
            pids_limit=args.pids_limit,
            lean_explore_directory=args.lean_explore_directory,
            huggingface_cache_directory=args.huggingface_cache_directory,
        )
    )
    schedule = run_job(manifest, runner, max_workers=args.max_workers)
    integration = integrate_modules(
        manifest,
        schedule,
        image=args.image,
    )
    print(
        json.dumps(
            {
                "status": integration.status,
                "job_id": manifest.job_id,
                "tasks": [
                    {
                        "id": task.task_id,
                        "artifact_file": str(task.artifact_file),
                        "artifact_sha256": task.artifact_sha256,
                        "contract_sha256": task.contract_sha256,
                    }
                    for task in schedule.tasks
                ],
                "integration_directory": str(
                    integration.integration_directory
                ),
                "integration_result": str(integration.result_file),
            },
            indent=2,
        )
    )


def main() -> None:
    args = _parser().parse_args()
    try:
        if args.command == "plan":
            _plan(args)
        else:
            _run(args)
    except (
        IntegrationError,
        ManifestError,
        PlanError,
        SandboxError,
        ScheduleError,
        ValueError,
    ) as error:
        print(f"Error: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
