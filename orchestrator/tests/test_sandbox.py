import hashlib
import json
from pathlib import Path

import pytest

from ..manifest import JobManifest, Task, load_manifest
from ..sandbox import (
    DockerSandboxConfig,
    DockerSandboxRunner,
    SandboxError,
    build_docker_command,
)


def _manifest(tmp_path: Path) -> tuple[JobManifest, Task]:
    specification = tmp_path / "spec.txt"
    specification.write_text("reviewed specification\n", encoding="utf-8")
    digest = hashlib.sha256(specification.read_bytes()).hexdigest()
    manifest_file = tmp_path / "job.json"
    manifest_file.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "job_id": "sandbox-job",
                "tasks": [
                    {
                        "id": "worker",
                        "input_file": "spec.txt",
                        "input_sha256": digest,
                        "output_file": "artifacts/Worker.lean",
                        "depends_on": [],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    manifest = load_manifest(manifest_file)
    return manifest, manifest.tasks[0]


def _option(command: list[str], name: str) -> str:
    return command[command.index(name) + 1]


def _mounted_host(command: list[str], container_path: str) -> Path:
    for index, argument in enumerate(command):
        if argument == "--volume":
            volume = command[index + 1]
            marker = f":{container_path}"
            if marker in volume:
                return Path(volume.split(marker, 1)[0])
    raise AssertionError(f"No mount found for {container_path}")


def test_docker_command_applies_isolation_and_does_not_embed_secret(
    monkeypatch,
    tmp_path: Path,
):
    _, task = _manifest(tmp_path)
    monkeypatch.setenv("OPENAI_API_KEY", "do-not-put-this-in-argv")
    command = build_docker_command(
        DockerSandboxConfig(
            image="leetproof-worker:test",
            provider="openai",
            model="test-model",
        ),
        task,
        session_name="session-001",
        state_directory=tmp_path / "state",
        artifacts_directory=tmp_path / "artifacts",
    )

    assert command[:2] == ["docker", "run"]
    assert "--rm" in command
    assert command[command.index("--cap-drop") + 1] == "ALL"
    assert (
        command[command.index("--security-opt") + 1]
        == "no-new-privileges:true"
    )
    assert command[command.index("--pids-limit") + 1] == "256"
    assert "OPENAI_API_KEY" in command
    assert "do-not-put-this-in-argv" not in command
    assert "DISABLE_LEAN_EXPLORE=1" in command
    assert command[-14:] == [
        "leetproof-worker:test",
        "pipeline",
        "--project",
        "/workspace",
        "--input-file",
        "/input/spec.txt",
        "--output-file",
        "/workspace/artifacts/Worker.lean",
        "--provider",
        "openai",
        "--model",
        "test-model",
        "--session-name",
        "session-001",
    ]


def test_docker_command_mounts_search_assets_read_only(tmp_path: Path):
    _, task = _manifest(tmp_path)
    lean_explore = tmp_path / "lean-explore"
    huggingface = tmp_path / "huggingface"
    lean_explore.mkdir()
    huggingface.mkdir()
    command = build_docker_command(
        DockerSandboxConfig(
            image="worker",
            provider="anthropic",
            model="model",
            lean_explore_directory=lean_explore,
            huggingface_cache_directory=huggingface,
        ),
        task,
        session_name="session",
        state_directory=tmp_path / "state",
        artifacts_directory=tmp_path / "artifacts",
    )

    assert f"{lean_explore.resolve()}:/home/worker/.lean_explore:ro" in command
    assert f"{huggingface.resolve()}:/home/worker/.cache/huggingface:ro" in command
    assert "HF_HUB_OFFLINE=1" in command
    assert "TRANSFORMERS_OFFLINE=1" in command
    assert "DISABLE_LEAN_EXPLORE=1" not in command


def test_runner_collects_artifact_and_result(monkeypatch, tmp_path: Path):
    manifest, task = _manifest(tmp_path)
    monkeypatch.setenv("OPENAI_API_KEY", "test-key")

    def fake_docker(command: list[str]) -> int:
        state = _mounted_host(command, "/workspace/.lloom")
        artifacts = _mounted_host(command, "/workspace/artifacts")
        session = _option(command, "--session-name")
        output_name = Path(_option(command, "--output-file")).name
        artifacts.mkdir(parents=True, exist_ok=True)
        (artifacts / output_name).write_text("verified candidate\n")
        result_directory = state / "sessions" / session
        result_directory.mkdir(parents=True, exist_ok=True)
        (result_directory / "Worker_result.json").write_text("{}\n")
        return 0

    runner = DockerSandboxRunner(
        DockerSandboxConfig(
            image="worker",
            provider="openai",
            model="model",
        ),
        command_runner=fake_docker,
    )

    result = runner.run_task(manifest, task)

    assert result.artifact_file.read_text() == "verified candidate\n"
    assert result.result_file.read_text() == "{}\n"
    assert result.run_directory.is_dir()
    assert result.session_name.startswith("sandbox-job-worker-")


def test_runner_preserves_run_data_after_container_failure(
    monkeypatch,
    tmp_path: Path,
):
    manifest, task = _manifest(tmp_path)
    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    runner = DockerSandboxRunner(
        DockerSandboxConfig(
            image="worker",
            provider="openai",
            model="model",
        ),
        command_runner=lambda _command: 17,
    )

    with pytest.raises(SandboxError, match="exit code 17; run data:"):
        runner.run_task(manifest, task)

    runs = list((tmp_path / ".orchestrator" / "runs" / "sandbox-job").iterdir())
    assert len(runs) == 1
    assert runs[0].is_dir()


def test_runner_requires_only_the_selected_provider_key(
    monkeypatch,
    tmp_path: Path,
):
    manifest, task = _manifest(tmp_path)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    runner = DockerSandboxRunner(
        DockerSandboxConfig(
            image="worker",
            provider="anthropic",
            model="model",
        ),
        command_runner=lambda _command: 0,
    )

    with pytest.raises(SandboxError, match="ANTHROPIC_API_KEY"):
        runner.run_task(manifest, task)
