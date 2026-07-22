"""Docker sandbox execution for one validated orchestrator task."""

from __future__ import annotations

import os
import subprocess
import tempfile
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from .manifest import JobManifest, Task


_PROVIDER_ENV = {
    "openai": "OPENAI_API_KEY",
    "anthropic": "ANTHROPIC_API_KEY",
    "google": "GOOGLE_API_KEY",
}


class SandboxError(RuntimeError):
    """Raised when an isolated worker cannot produce its artifacts."""


@dataclass(frozen=True)
class DockerSandboxConfig:
    image: str
    provider: str
    model: str
    cpus: float = 2
    memory: str = "8g"
    pids_limit: int = 256
    docker_binary: str = "docker"
    lean_explore_directory: Path | None = None
    huggingface_cache_directory: Path | None = None


@dataclass(frozen=True)
class SandboxResult:
    task_id: str
    session_name: str
    run_directory: Path
    artifact_file: Path
    result_file: Path


def _volume(host: Path, container: str, *, readonly: bool = False) -> str:
    suffix = ":ro" if readonly else ""
    return f"{host.resolve()}:{container}{suffix}"


def build_docker_command(
    config: DockerSandboxConfig,
    task: Task,
    *,
    session_name: str,
    state_directory: Path,
    artifacts_directory: Path,
) -> list[str]:
    """Build a shell-free, resource-bounded Docker invocation."""
    artifact_name = task.output_file.name
    container_output = f"/workspace/artifacts/{artifact_name}"
    command = [
        config.docker_binary,
        "run",
        "--rm",
        "--name",
        f"leetproof-{session_name}",
        "--cpus",
        str(config.cpus),
        "--memory",
        config.memory,
        "--pids-limit",
        str(config.pids_limit),
        "--cap-drop",
        "ALL",
        "--security-opt",
        "no-new-privileges:true",
        "--network",
        "bridge",
        "--stop-timeout",
        "30",
        "--tmpfs",
        "/tmp:rw,noexec,nosuid,size=1g",
        "--volume",
        _volume(task.input_file, "/input/spec.txt", readonly=True),
        "--volume",
        _volume(state_directory, "/workspace/.lloom"),
        "--volume",
        _volume(artifacts_directory, "/workspace/artifacts"),
    ]

    provider_key = _PROVIDER_ENV.get(config.provider)
    if provider_key is None:
        raise SandboxError(f"Unsupported provider: {config.provider}")
    command.extend(["--env", provider_key])
    if config.provider == "openai":
        for optional_name in ("OPENAI_BASE_URL", "OPENAI_API_BASE"):
            if os.environ.get(optional_name):
                command.extend(["--env", optional_name])

    lean_explore = config.lean_explore_directory
    huggingface_cache = config.huggingface_cache_directory
    if lean_explore is not None and huggingface_cache is not None:
        command.extend(
            [
                "--volume",
                _volume(
                    lean_explore,
                    "/home/worker/.lean_explore",
                    readonly=True,
                ),
                "--volume",
                _volume(
                    huggingface_cache,
                    "/home/worker/.cache/huggingface",
                    readonly=True,
                ),
                "--env",
                "HF_HUB_OFFLINE=1",
                "--env",
                "TRANSFORMERS_OFFLINE=1",
            ]
        )
    else:
        command.extend(["--env", "DISABLE_LEAN_EXPLORE=1"])

    command.extend(
        [
            config.image,
            "pipeline",
            "--project",
            "/workspace",
            "--input-file",
            "/input/spec.txt",
            "--output-file",
            container_output,
            "--provider",
            config.provider,
            "--model",
            config.model,
            "--session-name",
            session_name,
        ]
    )
    return command


class DockerSandboxRunner:
    """Run one task in a fresh, disposable Docker container."""

    def __init__(
        self,
        config: DockerSandboxConfig,
        *,
        command_runner: Callable[[list[str]], int] | None = None,
    ) -> None:
        self.config = config
        self._command_runner = command_runner or self._run_command

    @staticmethod
    def _run_command(command: list[str]) -> int:
        try:
            return subprocess.run(command, check=False).returncode
        except OSError as error:
            raise SandboxError(f"Could not start Docker: {error}") from error

    def run_task(self, manifest: JobManifest, task: Task) -> SandboxResult:
        provider_key = _PROVIDER_ENV.get(self.config.provider)
        if provider_key is None:
            raise SandboxError(f"Unsupported provider: {self.config.provider}")
        if not os.environ.get(provider_key):
            raise SandboxError(f"Required environment variable is not set: {provider_key}")

        for label, directory in (
            ("LeanExplore", self.config.lean_explore_directory),
            ("Hugging Face cache", self.config.huggingface_cache_directory),
        ):
            if directory is not None and not directory.is_dir():
                raise SandboxError(f"{label} directory does not exist: {directory}")
        if (self.config.lean_explore_directory is None) != (
            self.config.huggingface_cache_directory is None
        ):
            raise SandboxError(
                "LeanExplore and Hugging Face cache directories must be provided together"
            )

        runs_directory = (
            manifest.manifest_file.parent
            / ".orchestrator"
            / "runs"
            / manifest.job_id
        )
        runs_directory.mkdir(parents=True, exist_ok=True)
        run_directory = Path(
            tempfile.mkdtemp(prefix=f"{task.id}-", dir=runs_directory)
        )
        state_directory = run_directory / "state"
        artifacts_directory = run_directory / "artifacts"
        state_directory.mkdir()
        artifacts_directory.mkdir()
        state_directory.chmod(0o777)
        artifacts_directory.chmod(0o777)

        attempt_id = run_directory.name.removeprefix(f"{task.id}-")
        session_name = (
            f"{manifest.job_id}-{task.id}-{attempt_id}"
            .lower()
            .replace("_", "-")
        )
        command = build_docker_command(
            self.config,
            task,
            session_name=session_name,
            state_directory=state_directory,
            artifacts_directory=artifacts_directory,
        )
        exit_code = self._command_runner(command)

        artifact_file = artifacts_directory / task.output_file.name
        result_file = (
            state_directory
            / "sessions"
            / session_name
            / f"{task.output_file.stem}_result.json"
        )
        if exit_code != 0:
            raise SandboxError(
                f"Task {task.id} failed with exit code {exit_code}; "
                f"run data: {run_directory}"
            )
        if not result_file.is_file():
            raise SandboxError(
                f"Task {task.id} did not produce result JSON: {result_file}"
            )
        if not artifact_file.is_file():
            raise SandboxError(
                f"Task {task.id} did not produce artifact: {artifact_file}"
            )
        return SandboxResult(
            task_id=task.id,
            session_name=session_name,
            run_directory=run_directory,
            artifact_file=artifact_file,
            result_file=result_file,
        )
