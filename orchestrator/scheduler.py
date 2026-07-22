"""Bounded in-memory DAG scheduling and strict worker-result gating."""

from __future__ import annotations

import hashlib
import heapq
import json
import re
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol

from .manifest import JobManifest, Task
from .sandbox import SandboxResult


class ScheduleError(RuntimeError):
    """Raised when a worker or its verification result is rejected."""


class TaskRunner(Protocol):
    def run_task(self, manifest: JobManifest, task: Task) -> SandboxResult: ...


@dataclass(frozen=True)
class AcceptedTask:
    task_id: str
    artifact_file: Path
    artifact_sha256: str
    contract_file: Path
    contract_sha256: str
    result_file: Path


@dataclass(frozen=True)
class ScheduleResult:
    tasks: tuple[AcceptedTask, ...]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _remove_lean_comments(text: str) -> str:
    without_blocks = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return "\n".join(line.split("--", 1)[0] for line in without_blocks.splitlines())


def _contract_path(result: SandboxResult, value: Any) -> Path:
    if not isinstance(value, str):
        raise ScheduleError(f"Task {result.task_id} result has no contract file")
    normalized = value.replace("\\", "/")
    if normalized.startswith("/workspace/.lloom/"):
        relative = normalized.removeprefix("/workspace/.lloom/")
    elif normalized.startswith(".lloom/"):
        relative = normalized.removeprefix(".lloom/")
    else:
        raise ScheduleError(
            f"Task {result.task_id} contract path is outside worker state"
        )
    unresolved = result.run_directory / "state" / relative
    if unresolved.is_symlink():
        raise ScheduleError(f"Task {result.task_id} contract is a symbolic link")
    path = unresolved.resolve()
    state = (result.run_directory / "state").resolve()
    if not path.is_relative_to(state) or not path.is_file():
        raise ScheduleError(
            f"Task {result.task_id} contract artifact is missing: {path}"
        )
    return path


def validate_worker_result(result: SandboxResult) -> AcceptedTask:
    """Independently validate the worker result contract and artifact hashes."""
    if result.result_file.is_symlink() or result.artifact_file.is_symlink():
        raise ScheduleError(f"Task {result.task_id} returned a symbolic link")
    try:
        payload = json.loads(result.result_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ScheduleError(
            f"Task {result.task_id} result JSON is unreadable: {error}"
        ) from error
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise ScheduleError(f"Task {result.task_id} has unsupported result schema")
    if payload.get("status") != "SUCCESS":
        raise ScheduleError(f"Task {result.task_id} worker status is not SUCCESS")

    implementation = payload.get("implementation")
    if not isinstance(implementation, dict):
        raise ScheduleError(f"Task {result.task_id} has no implementation metadata")
    artifact_sha256 = _sha256(result.artifact_file)
    if implementation.get("sha256") != artifact_sha256:
        raise ScheduleError(f"Task {result.task_id} implementation hash mismatch")

    contract = payload.get("contract")
    if not isinstance(contract, dict):
        raise ScheduleError(f"Task {result.task_id} has no frozen contract metadata")
    contract_file = _contract_path(result, contract.get("file"))
    contract_sha256 = _sha256(contract_file)
    if contract.get("sha256") != contract_sha256:
        raise ScheduleError(f"Task {result.task_id} contract hash mismatch")

    verification = payload.get("verification")
    if not isinstance(verification, dict):
        raise ScheduleError(f"Task {result.task_id} has no verification summary")
    if verification.get("testcases_passed") is not True:
        raise ScheduleError(f"Task {result.task_id} test cases did not pass")
    if verification.get("pbt_status") != "ADDED_AND_PASSED":
        raise ScheduleError(f"Task {result.task_id} PBT did not pass")
    if verification.get("proof_status") != "PASSED":
        raise ScheduleError(f"Task {result.task_id} proof did not pass")
    if verification.get("goals_partial") not in (0, None):
        raise ScheduleError(f"Task {result.task_id} contains partial proof goals")

    stages = payload.get("stages")
    required_stages = ("specgen", "codegen", "invgen", "verify")
    if not isinstance(stages, dict) or any(
        not isinstance(stages.get(stage), dict)
        or stages[stage].get("status") != "SUCCESS"
        for stage in required_stages
    ):
        raise ScheduleError(f"Task {result.task_id} did not pass every pipeline stage")

    program = _remove_lean_comments(
        result.artifact_file.read_text(encoding="utf-8")
    )
    if re.search(r"\b(?:sorry|admit)\b", program):
        raise ScheduleError(f"Task {result.task_id} artifact contains sorry or admit")
    return AcceptedTask(
        task_id=result.task_id,
        artifact_file=result.artifact_file,
        artifact_sha256=artifact_sha256,
        contract_file=contract_file,
        contract_sha256=contract_sha256,
        result_file=result.result_file,
    )


def run_job(
    manifest: JobManifest,
    runner: TaskRunner,
    *,
    max_workers: int = 2,
) -> ScheduleResult:
    """Run ready DAG tasks with a small local worker pool."""
    if max_workers < 1:
        raise ValueError("max_workers must be at least 1")
    manifest.execution_order()
    tasks_by_id = {task.id: task for task in manifest.tasks}
    remaining = {task.id: len(task.depends_on) for task in manifest.tasks}
    dependents = {task.id: [] for task in manifest.tasks}
    for task in manifest.tasks:
        for dependency in task.depends_on:
            dependents[dependency].append(task.id)

    ready = [task_id for task_id, count in remaining.items() if count == 0]
    heapq.heapify(ready)
    accepted: dict[str, AcceptedTask] = {}
    running: dict[Future[AcceptedTask], str] = {}
    failure: ScheduleError | None = None

    def execute(task: Task) -> AcceptedTask:
        return validate_worker_result(runner.run_task(manifest, task))

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        while ready or running:
            while ready and len(running) < max_workers and failure is None:
                task_id = heapq.heappop(ready)
                running[pool.submit(execute, tasks_by_id[task_id])] = task_id
            if not running:
                break
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in sorted(completed, key=lambda item: running[item]):
                task_id = running.pop(future)
                try:
                    accepted_task = future.result()
                except Exception as error:
                    failure = ScheduleError(f"Task {task_id} failed: {error}")
                    ready.clear()
                    continue
                accepted[task_id] = accepted_task
                if failure is not None:
                    continue
                for dependent in sorted(dependents[task_id]):
                    remaining[dependent] -= 1
                    if remaining[dependent] == 0:
                        heapq.heappush(ready, dependent)

    if failure is not None:
        raise failure
    if len(accepted) != len(manifest.tasks):
        missing = sorted(set(tasks_by_id) - accepted.keys())
        raise ScheduleError("Tasks were not scheduled: " + ", ".join(missing))
    return ScheduleResult(
        tasks=tuple(accepted[task.id] for task in manifest.execution_order())
    )
