import hashlib
import json
import os
from pathlib import Path, PurePosixPath

import pytest

from ..integration import IntegrationError, _namespaced_source, integrate_modules
from ..manifest import JobManifest, Task
from ..scheduler import AcceptedTask, ScheduleResult, validate_worker_result
from .test_scheduler import _manifest, _sandbox_result


def _schedule(tmp_path: Path) -> tuple[JobManifest, ScheduleResult]:
    manifest = _manifest(tmp_path)
    accepted = tuple(
        validate_worker_result(_sandbox_result(tmp_path / "runs", task))
        for task in manifest.execution_order()
    )
    return manifest, ScheduleResult(accepted)


def test_namespaced_source_omits_redundant_pbt_command():
    source = """import Velvet.Std

method choose return (result : Nat)
do
  return 0

velvet_plausible_test choose
prove_correct choose by
  simp
"""

    wrapped = _namespaced_source(source, "Choose")

    assert "namespace Generated.Choose" in wrapped
    assert "-- velvet_plausible_test choose" in wrapped
    assert "prove_correct choose by" in wrapped


def test_integration_generates_import_module_and_verifies_it(tmp_path: Path):
    manifest, schedule = _schedule(tmp_path)
    observed: list[str] = []

    def fake_docker(command: list[str]) -> int:
        observed.extend(command)
        return 0

    result = integrate_modules(
        manifest,
        schedule,
        image="worker:test",
        command_runner=fake_docker,
    )

    assert result.status == "SUCCESS"
    assert result.import_file.read_text(encoding="utf-8") == (
        "import Generated.Alpha\n"
        "import Generated.Beta\n"
        "import Generated.Final\n"
    )
    assert (
        result.integration_directory / "Alpha.lean"
    ).read_text(encoding="utf-8") == (
        "import Extensions\n"
        "\n"
        "namespace Generated.Alpha\n"
        "\n"
        "def AlphaValue : Nat := 1\n"
        "end Generated.Alpha\n"
    )
    assert "worker:test" in observed
    assert observed[-2:] == [
        "worker:test",
        "/workspace/Generated/verify.sh",
    ]
    assert (
        result.integration_directory / "verify.sh"
    ).read_text(encoding="utf-8").endswith("lean Generated/All.lean\n")
    payload = json.loads(result.result_file.read_text(encoding="utf-8"))
    assert payload["status"] == "SUCCESS"
    assert [module["task_id"] for module in payload["modules"]] == [
        "alpha",
        "beta",
        "final",
    ]
    assert payload["modules"][0]["namespace"] == "Generated.Alpha"
    assert payload["modules"][0]["source_sha256"] == (
        schedule.tasks[0].artifact_sha256
    )


def test_integration_preserves_failed_attempt_result(tmp_path: Path):
    manifest, schedule = _schedule(tmp_path)

    with pytest.raises(IntegrationError, match="exit code 9"):
        integrate_modules(
            manifest,
            schedule,
            image="worker:test",
            command_runner=lambda _command: 9,
        )

    results = list(
        (
            tmp_path
            / ".orchestrator"
            / "integrations"
            / manifest.job_id
        ).glob("attempt-*/integration_result.json")
    )
    assert len(results) == 1
    assert json.loads(results[0].read_text(encoding="utf-8"))["status"] == "FAILED"


@pytest.mark.skipif(
    os.environ.get("RUN_DOCKER_TESTS") != "1",
    reason="set RUN_DOCKER_TESTS=1 for the worker-image smoke test",
)
def test_integration_with_worker_image(tmp_path: Path):
    artifact = tmp_path / "Smoke.lean"
    artifact.write_text(
        "import Extensions\n\ndef smokeValue : Nat := 1\n",
        encoding="utf-8",
    )
    contract = tmp_path / "Smoke.contract.lean"
    contract.write_text("import Extensions\n", encoding="utf-8")
    task = Task(
        "smoke",
        tmp_path / "smoke.txt",
        "0" * 64,
        PurePosixPath("artifacts/Smoke.lean"),
        (),
    )
    manifest = JobManifest(
        1,
        "docker-smoke",
        tmp_path / "job.json",
        (task,),
    )
    accepted = AcceptedTask(
        task_id="smoke",
        artifact_file=artifact,
        artifact_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),
        contract_file=contract,
        contract_sha256=hashlib.sha256(contract.read_bytes()).hexdigest(),
        result_file=tmp_path / "result.json",
    )

    result = integrate_modules(
        manifest,
        ScheduleResult((accepted,)),
        image=os.environ.get("LEETPROOF_WORKER_IMAGE", "leetproof-worker:1"),
    )

    assert result.status == "SUCCESS"


@pytest.mark.skipif(
    os.environ.get("RUN_DOCKER_TESTS") != "1",
    reason="set RUN_DOCKER_TESTS=1 for the worker-image smoke test",
)
def test_integration_namespaces_duplicate_declarations(tmp_path: Path):
    tasks = tuple(
        Task(
            name.casefold(),
            tmp_path / f"{name}.txt",
            "0" * 64,
            PurePosixPath(f"artifacts/{name}.lean"),
            (),
        )
        for name in ("Alpha", "Beta")
    )
    manifest = JobManifest(
        1,
        "namespace-smoke",
        tmp_path / "job.json",
        tasks,
    )
    accepted = []
    for task in tasks:
        artifact = tmp_path / task.output_file.name
        artifact.write_text(
            "\n".join(
                [
                    "import Mathlib",
                    "",
                    "def precondition : Prop := True",
                        "def postcondition (value : Nat) : Prop :=",
                        "  value = 0",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        contract = tmp_path / f"{task.output_file.stem}.contract.lean"
        contract.write_text("import Mathlib\n", encoding="utf-8")
        accepted.append(
            AcceptedTask(
                task_id=task.id,
                artifact_file=artifact,
                artifact_sha256=hashlib.sha256(
                    artifact.read_bytes()
                ).hexdigest(),
                contract_file=contract,
                contract_sha256=hashlib.sha256(
                    contract.read_bytes()
                ).hexdigest(),
                result_file=tmp_path / f"{task.id}-result.json",
            )
        )

    result = integrate_modules(
        manifest,
        ScheduleResult(tuple(accepted)),
        image=os.environ.get("LEETPROOF_WORKER_IMAGE", "leetproof-worker:1"),
    )

    assert result.status == "SUCCESS"
