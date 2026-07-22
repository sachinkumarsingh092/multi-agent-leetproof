import hashlib
import json
from pathlib import Path

import pytest

from ..manifest import ManifestError, load_manifest


def _write_spec(directory: Path, name: str) -> Path:
    path = directory / f"{name}.txt"
    path.write_text(f"reviewed specification for {name}\n", encoding="utf-8")
    return path


def _task(
    input_file: Path,
    task_id: str,
    *,
    depends_on: list[str] | None = None,
    output_file: str | None = None,
    digest: str | None = None,
) -> dict:
    return {
        "id": task_id,
        "input_file": input_file.name,
        "input_sha256": digest
        or hashlib.sha256(input_file.read_bytes()).hexdigest(),
        "output_file": output_file or f"artifacts/{task_id}.lean",
        "depends_on": depends_on or [],
    }


def _write_manifest(directory: Path, tasks: list[dict]) -> Path:
    path = directory / "job.json"
    path.write_text(
        json.dumps(
            {
                "$schema": "job.schema.json",
                "schema_version": 1,
                "job_id": "test-job",
                "tasks": tasks,
            }
        ),
        encoding="utf-8",
    )
    return path


def test_valid_manifest_has_deterministic_dependency_order(tmp_path: Path):
    core = _write_spec(tmp_path, "core")
    alpha = _write_spec(tmp_path, "alpha")
    beta = _write_spec(tmp_path, "beta")
    final = _write_spec(tmp_path, "final")
    manifest_file = _write_manifest(
        tmp_path,
        [
            _task(final, "final", depends_on=["beta", "alpha"]),
            _task(beta, "beta", depends_on=["core"]),
            _task(core, "core"),
            _task(alpha, "alpha", depends_on=["core"]),
        ],
    )

    manifest = load_manifest(manifest_file)

    assert manifest.schema_version == 1
    assert manifest.job_id == "test-job"
    assert [task.id for task in manifest.execution_order()] == [
        "core",
        "alpha",
        "beta",
        "final",
    ]
    assert manifest.execution_order()[0].input_file == core.resolve()


def test_duplicate_task_ids_are_rejected(tmp_path: Path):
    spec = _write_spec(tmp_path, "spec")
    manifest_file = _write_manifest(
        tmp_path,
        [
            _task(spec, "same", output_file="First.lean"),
            _task(spec, "same", output_file="Second.lean"),
        ],
    )

    with pytest.raises(ManifestError, match="Task IDs must be unique"):
        load_manifest(manifest_file)


def test_unknown_dependency_is_rejected(tmp_path: Path):
    spec = _write_spec(tmp_path, "spec")
    manifest_file = _write_manifest(
        tmp_path,
        [_task(spec, "task", depends_on=["missing"])],
    )

    with pytest.raises(ManifestError, match="unknown dependencies: missing"):
        load_manifest(manifest_file)


def test_dependency_cycle_is_rejected(tmp_path: Path):
    first = _write_spec(tmp_path, "first")
    second = _write_spec(tmp_path, "second")
    manifest_file = _write_manifest(
        tmp_path,
        [
            _task(first, "first", depends_on=["second"]),
            _task(second, "second", depends_on=["first"]),
        ],
    )

    with pytest.raises(ManifestError, match="cycle involving: first, second"):
        load_manifest(manifest_file)


def test_input_hash_mismatch_is_rejected(tmp_path: Path):
    spec = _write_spec(tmp_path, "spec")
    manifest_file = _write_manifest(
        tmp_path,
        [_task(spec, "task", digest="0" * 64)],
    )

    with pytest.raises(ManifestError, match="input_sha256 does not match"):
        load_manifest(manifest_file)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("input_file", "../outside.txt"),
        ("output_file", "../outside.lean"),
        ("output_file", "/absolute.lean"),
    ],
)
def test_paths_cannot_escape_job_directory(
    tmp_path: Path,
    field: str,
    value: str,
):
    spec = _write_spec(tmp_path, "spec")
    task = _task(spec, "task")
    task[field] = value
    manifest_file = _write_manifest(tmp_path, [task])

    with pytest.raises(ManifestError, match="must stay within the job directory"):
        load_manifest(manifest_file)


def test_duplicate_outputs_are_rejected(tmp_path: Path):
    first = _write_spec(tmp_path, "first")
    second = _write_spec(tmp_path, "second")
    manifest_file = _write_manifest(
        tmp_path,
        [
            _task(first, "first", output_file="Shared.lean"),
            _task(second, "second", output_file="shared.lean"),
        ],
    )

    with pytest.raises(ManifestError, match="output_file values must be unique"):
        load_manifest(manifest_file)


def test_unknown_manifest_fields_are_rejected(tmp_path: Path):
    spec = _write_spec(tmp_path, "spec")
    manifest_file = _write_manifest(tmp_path, [_task(spec, "task")])
    raw = json.loads(manifest_file.read_text(encoding="utf-8"))
    raw["unexpected"] = True
    manifest_file.write_text(json.dumps(raw), encoding="utf-8")

    with pytest.raises(ManifestError, match="unknown fields: unexpected"):
        load_manifest(manifest_file)


def test_boolean_schema_version_is_rejected(tmp_path: Path):
    spec = _write_spec(tmp_path, "spec")
    manifest_file = _write_manifest(tmp_path, [_task(spec, "task")])
    raw = json.loads(manifest_file.read_text(encoding="utf-8"))
    raw["schema_version"] = True
    manifest_file.write_text(json.dumps(raw), encoding="utf-8")

    with pytest.raises(ManifestError, match="Unsupported schema_version"):
        load_manifest(manifest_file)
