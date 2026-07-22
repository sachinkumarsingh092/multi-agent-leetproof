import hashlib
import json
import threading
from pathlib import Path, PurePosixPath

import pytest

from ..manifest import JobManifest, Task
from ..sandbox import SandboxResult
from ..scheduler import ScheduleError, run_job, validate_worker_result


def _manifest(tmp_path: Path) -> JobManifest:
    tasks = (
        Task(
            "alpha",
            tmp_path / "alpha.txt",
            "a" * 64,
            PurePosixPath("Alpha.lean"),
            (),
        ),
        Task(
            "beta",
            tmp_path / "beta.txt",
            "b" * 64,
            PurePosixPath("Beta.lean"),
            (),
        ),
        Task(
            "final",
            tmp_path / "final.txt",
            "c" * 64,
            PurePosixPath("Final.lean"),
            ("alpha", "beta"),
        ),
    )
    return JobManifest(1, "scheduled-job", tmp_path / "job.json", tasks)


def _sandbox_result(root: Path, task: Task) -> SandboxResult:
    run = root / task.id
    session = f"session-{task.id}"
    artifacts = run / "artifacts"
    result_directory = run / "state" / "sessions" / session
    contracts = result_directory / "contracts"
    artifacts.mkdir(parents=True)
    contracts.mkdir(parents=True)
    artifact = artifacts / task.output_file.name
    artifact.write_text(
        f"import Extensions\n\ndef {task.output_file.stem}Value : Nat := 1\n",
        encoding="utf-8",
    )
    contract = contracts / f"{task.output_file.stem}.contract.lean"
    contract.write_text("import Extensions\n", encoding="utf-8")
    result_file = result_directory / f"{task.output_file.stem}_result.json"
    result_file.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "status": "SUCCESS",
                "contract": {
                    "file": (
                        f".lloom/sessions/{session}/contracts/"
                        f"{task.output_file.stem}.contract.lean"
                    ),
                    "sha256": hashlib.sha256(contract.read_bytes()).hexdigest(),
                },
                "implementation": {
                    "file": f"/workspace/artifacts/{task.output_file.name}",
                    "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
                },
                "verification": {
                    "testcases_passed": True,
                    "pbt_status": "ADDED_AND_PASSED",
                    "proof_status": "PASSED",
                    "goals_partial": 0,
                },
                "stages": {
                    stage: {"status": "SUCCESS"}
                    for stage in ("specgen", "codegen", "invgen", "verify")
                },
            }
        ),
        encoding="utf-8",
    )
    return SandboxResult(
        task_id=task.id,
        session_name=session,
        run_directory=run,
        artifact_file=artifact,
        result_file=result_file,
    )


def test_scheduler_runs_ready_tasks_before_dependent_task(tmp_path: Path):
    manifest = _manifest(tmp_path)
    barrier = threading.Barrier(2)
    completed: set[str] = set()
    lock = threading.Lock()

    class FakeRunner:
        def run_task(self, manifest: JobManifest, task: Task) -> SandboxResult:
            assert manifest.job_id == "scheduled-job"
            if not task.depends_on:
                barrier.wait(timeout=2)
            else:
                with lock:
                    assert set(task.depends_on) <= completed
            result = _sandbox_result(tmp_path / "runs", task)
            with lock:
                completed.add(task.id)
            return result

    schedule = run_job(manifest, FakeRunner(), max_workers=2)

    assert [task.task_id for task in schedule.tasks] == [
        "alpha",
        "beta",
        "final",
    ]
    assert completed == {"alpha", "beta", "final"}


def test_result_gate_rejects_implementation_hash_mismatch(tmp_path: Path):
    task = _manifest(tmp_path).tasks[0]
    result = _sandbox_result(tmp_path / "runs", task)
    result.artifact_file.write_text("def changed := true\n", encoding="utf-8")

    with pytest.raises(ScheduleError, match="implementation hash mismatch"):
        validate_worker_result(result)


def test_result_gate_requires_successful_pbt(tmp_path: Path):
    task = _manifest(tmp_path).tasks[0]
    result = _sandbox_result(tmp_path / "runs", task)
    payload = json.loads(result.result_file.read_text(encoding="utf-8"))
    payload["verification"]["pbt_status"] = "NOT_ADDED"
    result.result_file.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ScheduleError, match="PBT did not pass"):
        validate_worker_result(result)


def test_scheduler_does_not_release_dependents_after_failure(tmp_path: Path):
    manifest = _manifest(tmp_path)
    started: list[str] = []

    class FailingRunner:
        def run_task(self, manifest: JobManifest, task: Task) -> SandboxResult:
            assert manifest.job_id == "scheduled-job"
            started.append(task.id)
            result = _sandbox_result(tmp_path / "runs", task)
            if task.id == "alpha":
                payload = json.loads(result.result_file.read_text(encoding="utf-8"))
                payload["status"] = "FAILED"
                result.result_file.write_text(json.dumps(payload), encoding="utf-8")
            return result

    with pytest.raises(ScheduleError, match="Task alpha failed"):
        run_job(manifest, FailingRunner(), max_workers=2)

    assert "final" not in started
