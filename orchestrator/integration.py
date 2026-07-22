"""Deterministically combine accepted modules and verify their imports."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import tempfile
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from .manifest import JobManifest
from .scheduler import ScheduleResult


class IntegrationError(RuntimeError):
    """Raised when accepted modules do not compose into one Lean project."""


@dataclass(frozen=True)
class IntegrationResult:
    status: str
    integration_directory: Path
    import_file: Path
    result_file: Path


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, payload: dict) -> None:
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def _run_command(command: list[str]) -> int:
    try:
        return subprocess.run(command, check=False).returncode
    except OSError as error:
        raise IntegrationError(f"Could not start Docker: {error}") from error


def _namespaced_source(source: str, module_name: str) -> str:
    """Wrap declarations while keeping Lean imports at module scope."""
    lines = source.splitlines()
    import_indices = [
        index
        for index, line in enumerate(lines)
        if re.match(r"^\s*import\s+\S+", line)
    ]
    split_at = import_indices[-1] + 1 if import_indices else 0
    namespace = f"Generated.{module_name}"
    prefix = lines[:split_at]
    body = []
    for line in lines[split_at:]:
        pbt_command = re.match(r"^(\s*)velvet_plausible_test\b", line)
        if pbt_command:
            indentation = pbt_command.group(1)
            body.extend(
                [
                    (
                        f"{indentation}-- Integration omitted this command: "
                        "PBT passed before namespacing."
                    ),
                    f"{indentation}-- {line.strip()}",
                ]
            )
        else:
            body.append(line)
    wrapped = [
        *prefix,
        "",
        f"namespace {namespace}",
        *body,
        f"end {namespace}",
    ]
    return "\n".join(wrapped) + "\n"


def integrate_modules(
    manifest: JobManifest,
    schedule: ScheduleResult,
    *,
    image: str,
    docker_binary: str = "docker",
    command_runner: Callable[[list[str]], int] | None = None,
) -> IntegrationResult:
    """Copy accepted modules, import all of them, and run Lean offline."""
    accepted_by_id = {task.task_id: task for task in schedule.tasks}
    if set(accepted_by_id) != {task.id for task in manifest.tasks}:
        raise IntegrationError("Accepted task set does not match the job manifest")

    root = (
        manifest.manifest_file.parent
        / ".orchestrator"
        / "integrations"
        / manifest.job_id
    )
    root.mkdir(parents=True, exist_ok=True)
    integration_directory = Path(
        tempfile.mkdtemp(prefix="attempt-", dir=root)
    )
    module_names: list[str] = []
    modules: list[dict[str, str]] = []
    for task in manifest.execution_order():
        module_name = task.output_file.stem
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", module_name):
            raise IntegrationError(
                f"Task {task.id} output stem is not a Lean module name: {module_name}"
            )
        if module_name.casefold() == "all":
            raise IntegrationError("Task output module name All is reserved")
        accepted = accepted_by_id[task.id]
        if _sha256(accepted.artifact_file) != accepted.artifact_sha256:
            raise IntegrationError(f"Task {task.id} artifact changed after acceptance")
        destination = integration_directory / f"{module_name}.lean"
        destination.write_text(
            _namespaced_source(
                accepted.artifact_file.read_text(encoding="utf-8"),
                module_name,
            ),
            encoding="utf-8",
        )
        module_names.append(module_name)
        modules.append(
            {
                "task_id": task.id,
                "module": module_name,
                "namespace": f"Generated.{module_name}",
                "file": str(destination),
                "source_sha256": accepted.artifact_sha256,
                "sha256": _sha256(destination),
            }
        )
    if len({name.casefold() for name in module_names}) != len(module_names):
        raise IntegrationError("Accepted artifacts have duplicate module names")

    import_file = integration_directory / "All.lean"
    import_file.write_text(
        "\n".join(f"import Generated.{name}" for name in module_names) + "\n",
        encoding="utf-8",
    )
    verification_script = integration_directory / "verify.sh"
    verification_script.write_text(
        "\n".join(
            [
                "#!/bin/sh",
                "set -eu",
                'BASE_LEAN_PATH="$(lake env printenv LEAN_PATH)"',
                'export LEAN_PATH="/tmp:${BASE_LEAN_PATH}"',
                "mkdir -p /tmp/Generated",
                *[
                    (
                        f"lean -o /tmp/Generated/{name}.olean "
                        f"Generated/{name}.lean"
                    )
                    for name in module_names
                ],
                "lean Generated/All.lean",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    result_file = integration_directory / "integration_result.json"
    payload = {
        "schema_version": 1,
        "job_id": manifest.job_id,
        "status": "RUNNING",
        "modules": modules,
        "import_file": str(import_file),
        "import_sha256": _sha256(import_file),
        "verification_script_sha256": _sha256(verification_script),
        "error": None,
    }
    _write_json(result_file, payload)

    container_name = (
        f"leetproof-integration-{manifest.job_id}-"
        f"{integration_directory.name.removeprefix('attempt-')}"
    ).lower().replace("_", "-")
    command = [
        docker_binary,
        "run",
        "--rm",
        "--name",
        container_name,
        "--network",
        "none",
        "--cpus",
        "2",
        "--memory",
        "8g",
        "--pids-limit",
        "256",
        "--cap-drop",
        "ALL",
        "--security-opt",
        "no-new-privileges:true",
        "--tmpfs",
        "/tmp:rw,noexec,nosuid,size=1g",
        "--volume",
        f"{integration_directory.resolve()}:/workspace/Generated:ro",
        "--entrypoint",
        "/bin/sh",
        image,
        "/workspace/Generated/verify.sh",
    ]
    exit_code = (command_runner or _run_command)(command)
    if exit_code != 0:
        payload["status"] = "FAILED"
        payload["error"] = {
            "type": "LeanIntegrationFailure",
            "message": f"Lean integration exited with code {exit_code}",
        }
        _write_json(result_file, payload)
        raise IntegrationError(
            f"Combined Lean verification failed with exit code {exit_code}; "
            f"run data: {integration_directory}"
        )

    payload["status"] = "SUCCESS"
    _write_json(result_file, payload)
    return IntegrationResult(
        status="SUCCESS",
        integration_directory=integration_directory,
        import_file=import_file,
        result_file=result_file,
    )
