"""Versioned job manifest loading for the external LeetProof orchestrator."""

from __future__ import annotations

import hashlib
import heapq
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any


SCHEMA_VERSION = 1
_ID_PATTERN = re.compile(r"^[A-Za-z][A-Za-z0-9_-]*$")
_SHA256_PATTERN = re.compile(r"^[0-9a-f]{64}$")


class ManifestError(ValueError):
    """Raised when a job manifest cannot be safely executed."""


@dataclass(frozen=True)
class Task:
    """One isolated, single-method worker task."""

    id: str
    input_file: Path
    input_sha256: str
    output_file: PurePosixPath
    depends_on: tuple[str, ...]


@dataclass(frozen=True)
class JobManifest:
    """Validated orchestration job and its deterministic task graph."""

    schema_version: int
    job_id: str
    manifest_file: Path
    tasks: tuple[Task, ...]

    def execution_order(self) -> tuple[Task, ...]:
        """Return a stable topological order, rejecting dependency cycles."""
        tasks_by_id = {task.id: task for task in self.tasks}
        indegree = {
            task.id: len(task.depends_on)
            for task in self.tasks
        }
        dependents: dict[str, list[str]] = {
            task.id: [] for task in self.tasks
        }
        for task in self.tasks:
            for dependency in task.depends_on:
                dependents[dependency].append(task.id)

        ready = [task_id for task_id, count in indegree.items() if count == 0]
        heapq.heapify(ready)
        ordered: list[Task] = []
        while ready:
            task_id = heapq.heappop(ready)
            ordered.append(tasks_by_id[task_id])
            for dependent in sorted(dependents[task_id]):
                indegree[dependent] -= 1
                if indegree[dependent] == 0:
                    heapq.heappush(ready, dependent)

        if len(ordered) != len(self.tasks):
            cyclic = sorted(
                task_id for task_id, count in indegree.items() if count > 0
            )
            raise ManifestError(
                "Task dependency graph contains a cycle involving: "
                + ", ".join(cyclic)
            )
        return tuple[Task, ...](ordered)


def _validate_keys(
    value: dict[str, Any],
    *,
    required: set[str],
    optional: set[str] | frozenset[str] = frozenset(),
    context: str,
) -> None:
    missing = sorted(required - value.keys())
    unknown = sorted(value.keys() - required - optional)
    if missing:
        raise ManifestError(f"{context} is missing fields: {', '.join(missing)}")
    if unknown:
        raise ManifestError(f"{context} has unknown fields: {', '.join(unknown)}")


def _identifier(value: Any, field: str) -> str:
    if not isinstance(value, str) or not _ID_PATTERN.fullmatch(value):
        raise ManifestError(
            f"{field} must start with a letter and contain only letters, "
            "numbers, '_' or '-'"
        )
    return value


def _relative_path(value: Any, field: str, suffix: str) -> PurePosixPath:
    if not isinstance(value, str) or not value or "\\" in value:
        raise ManifestError(f"{field} must be a non-empty POSIX path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts:
        raise ManifestError(f"{field} must stay within the job directory")
    if path.suffix != suffix:
        raise ManifestError(f"{field} must end with {suffix}")
    return path


def _load_task(
    raw: Any,
    *,
    index: int,
    job_directory: Path,
) -> Task:
    context = f"tasks[{index}]"
    if not isinstance(raw, dict):
        raise ManifestError(f"{context} must be an object")
    _validate_keys(
        raw,
        required={
            "id",
            "input_file",
            "input_sha256",
            "output_file",
            "depends_on",
        },
        context=context,
    )

    task_id = _identifier(raw["id"], f"{context}.id")
    input_relative = _relative_path(
        raw["input_file"],
        f"{context}.input_file",
        ".txt",
    )
    output_file = _relative_path(
        raw["output_file"],
        f"{context}.output_file",
        ".lean",
    )
    digest = raw["input_sha256"]
    if not isinstance(digest, str) or not _SHA256_PATTERN.fullmatch(digest):
        raise ManifestError(
            f"{context}.input_sha256 must be a lowercase SHA-256 digest"
        )

    dependencies = raw["depends_on"]
    if not isinstance(dependencies, list):
        raise ManifestError(f"{context}.depends_on must be an array")
    depends_on = tuple(
        _identifier(dependency, f"{context}.depends_on")
        for dependency in dependencies
    )
    if len(depends_on) != len(set(depends_on)):
        raise ManifestError(f"{context}.depends_on contains duplicates")
    if task_id in depends_on:
        raise ManifestError(f"{context} cannot depend on itself")

    input_file = (job_directory / Path(*input_relative.parts)).resolve()
    if not input_file.is_relative_to(job_directory):
        raise ManifestError(f"{context}.input_file resolves outside the job directory")
    if not input_file.is_file():
        raise ManifestError(f"{context}.input_file does not exist: {input_relative}")
    actual_digest = hashlib.sha256(input_file.read_bytes()).hexdigest()
    if actual_digest != digest:
        raise ManifestError(
            f"{context}.input_sha256 does not match {input_relative}"
        )

    return Task(
        id=task_id,
        input_file=input_file,
        input_sha256=digest,
        output_file=output_file,
        depends_on=depends_on,
    )


def load_manifest(manifest_file: str | Path) -> JobManifest:
    """Load, validate, hash-check, and order a version-1 job manifest."""
    path = Path(manifest_file).resolve()
    if not path.is_file():
        raise ManifestError(f"Manifest file does not exist: {path}")
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise ManifestError(f"Manifest is not valid JSON: {error}") from error
    if not isinstance(raw, dict):
        raise ManifestError("Manifest root must be an object")
    _validate_keys(
        raw,
        required={"schema_version", "job_id", "tasks"},
        optional={"$schema"},
        context="manifest",
    )
    if "$schema" in raw and not isinstance(raw["$schema"], str):
        raise ManifestError("$schema must be a string")
    version = raw["schema_version"]
    if (
        not isinstance(version, int)
        or isinstance(version, bool)
        or version != SCHEMA_VERSION
    ):
        raise ManifestError(
            f"Unsupported schema_version {version!r}; "
            f"expected {SCHEMA_VERSION}"
        )
    job_id = _identifier(raw["job_id"], "job_id")
    raw_tasks = raw["tasks"]
    if not isinstance(raw_tasks, list) or not raw_tasks:
        raise ManifestError("tasks must be a non-empty array")

    job_directory = path.parent.resolve()
    tasks = tuple(
        _load_task(task, index=index, job_directory=job_directory)
        for index, task in enumerate(raw_tasks)
    )
    task_ids = [task.id for task in tasks]
    if len(task_ids) != len(set(task_ids)):
        raise ManifestError("Task IDs must be unique")
    output_files = [str(task.output_file).casefold() for task in tasks]
    if len(output_files) != len(set(output_files)):
        raise ManifestError("Task output_file values must be unique")

    known_ids = set(task_ids)
    for task in tasks:
        missing = sorted(set(task.depends_on) - known_ids)
        if missing:
            raise ManifestError(
                f"Task {task.id} has unknown dependencies: {', '.join(missing)}"
            )

    manifest = JobManifest(
        schema_version=SCHEMA_VERSION,
        job_id=job_id,
        manifest_file=path,
        tasks=tasks,
    )
    manifest.execution_order()
    return manifest
