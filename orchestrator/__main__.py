"""Command-line entry point for one-task sandbox execution."""

import argparse
import json
import sys
from pathlib import Path

from .manifest import ManifestError, load_manifest
from .sandbox import (
    DockerSandboxConfig,
    DockerSandboxRunner,
    SandboxError,
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run one validated LeetProof task in Docker",
    )
    parser.add_argument("manifest", help="Path to job.json")
    parser.add_argument(
        "--task-id",
        help="Task to run; optional only when the manifest has one task",
    )
    parser.add_argument("--image", default="leetproof-worker:1")
    parser.add_argument(
        "--provider",
        required=True,
        choices=("openai", "anthropic", "google"),
    )
    parser.add_argument("--model", required=True)
    parser.add_argument("--cpus", type=float, default=2)
    parser.add_argument("--memory", default="8g")
    parser.add_argument("--pids-limit", type=int, default=256)
    parser.add_argument("--lean-explore-directory", type=Path)
    parser.add_argument("--huggingface-cache-directory", type=Path)
    return parser


def main() -> None:
    args = _parser().parse_args()
    try:
        manifest = load_manifest(args.manifest)
        if args.task_id:
            task = next(
                (task for task in manifest.tasks if task.id == args.task_id),
                None,
            )
            if task is None:
                raise ManifestError(f"Unknown task ID: {args.task_id}")
        elif len(manifest.tasks) == 1:
            task = manifest.tasks[0]
        else:
            raise ManifestError(
                "--task-id is required when the manifest contains multiple tasks"
            )

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
        result = runner.run_task(manifest, task)
    except (ManifestError, SandboxError) as error:
        print(f"Error: {error}", file=sys.stderr)
        raise SystemExit(1) from error

    print(
        json.dumps(
            {
                "task_id": result.task_id,
                "session_name": result.session_name,
                "run_directory": str(result.run_directory),
                "artifact_file": str(result.artifact_file),
                "result_file": str(result.result_file),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
