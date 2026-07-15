"""Tests for Aristotle submit/check script helpers."""

from __future__ import annotations

import json
import asyncio
import sys
import tarfile
from enum import Enum
from pathlib import Path
from types import SimpleNamespace

from scripts import aristotle_submit
from utils.aristotle_helpers import _extract_member_from_tarball


class FakeProjectStatus(Enum):
    COMPLETE = "COMPLETE"
    COMPLETE_WITH_ERRORS = "COMPLETE_WITH_ERRORS"
    OUT_OF_BUDGET = "OUT_OF_BUDGET"
    IN_PROGRESS = "IN_PROGRESS"
    FAILED = "FAILED"
    CANCELED = "CANCELED"
    UNKNOWN = "UNKNOWN"


def test_run_check_marks_terminal_failure_and_stops_tracking(tmp_path, monkeypatch, capsys):
    jobs_file = tmp_path / "aristotle_jobs.json"
    jobs_file.write_text(json.dumps([
        {
            "input_file": "Example.lean",
            "project_id": "proj-1",
            "status": "pending",
            "submitted_at": "2026-03-21T00:00:00+00:00",
            "output_file": "ExampleAristotleProof.lean",
        }
    ]))

    monkeypatch.setitem(
        sys.modules,
        "aristotlelib",
        SimpleNamespace(ProjectStatus=FakeProjectStatus),
    )
    monkeypatch.setitem(
        sys.modules,
        "utils.aristotle_helpers",
        SimpleNamespace(
            get_submission_status=_fake_async(FakeProjectStatus.CANCELED),
            get_submission=_fake_async(None),
        ),
    )

    asyncio.run(aristotle_submit._run_check(jobs_file))

    jobs = json.loads(jobs_file.read_text())
    assert jobs[0]["status"] == "failed"
    assert jobs[0]["api_status"] == "CANCELED"
    assert "completed_at" in jobs[0]
    assert "terminal" in capsys.readouterr().out


def test_run_check_downloads_completed_job(tmp_path, monkeypatch):
    jobs_file = tmp_path / "aristotle_jobs.json"
    output_file = tmp_path / "ExampleAristotleProof.lean"
    jobs_file.write_text(json.dumps([
        {
            "input_file": "Example.lean",
            "project_id": "proj-2",
            "status": "pending",
            "submitted_at": "2026-03-21T00:00:00+00:00",
            "output_file": str(output_file),
        }
    ]))

    async def fake_get_submission(
        project_id: str,
        path: str | Path | None = None,
        project_root: str | Path | None = None,
    ) -> Path:
        assert project_id == "proj-2"
        assert project_root == tmp_path
        saved_path = Path(path)
        saved_path.write_text("-- solution")
        return saved_path

    monkeypatch.setitem(
        sys.modules,
        "aristotlelib",
        SimpleNamespace(ProjectStatus=FakeProjectStatus),
    )
    monkeypatch.setitem(
        sys.modules,
        "utils.aristotle_helpers",
        SimpleNamespace(
            get_submission_status=_fake_async(FakeProjectStatus.COMPLETE),
            get_submission=fake_get_submission,
        ),
    )

    asyncio.run(aristotle_submit._run_check(jobs_file))

    jobs = json.loads(jobs_file.read_text())
    assert jobs[0]["status"] == "done"
    assert jobs[0]["api_status"] == "COMPLETE"
    assert output_file.read_text() == "-- solution"


def test_extract_member_from_tarball_falls_back_to_matching_lean_basename(tmp_path):
    archive_path = tmp_path / "result.tar.gz"
    source_dir = tmp_path / "src"
    source_dir.mkdir()
    nested = source_dir / "RequestProject"
    nested.mkdir()
    target = nested / "FooAristotleProof.lean"
    target.write_text("-- solved proof")
    (nested / "ARISTOTLE_SUMMARY_123.md").write_text("summary")

    with tarfile.open(archive_path, "w:gz") as archive:
        archive.add(target, arcname="RequestProject/FooAristotleProof.lean")
        archive.add(
            nested / "ARISTOTLE_SUMMARY_123.md",
            arcname="RequestProject/ARISTOTLE_SUMMARY_123.md",
        )

    destination = tmp_path / "out" / "FooAristotleProof.lean"
    saved = _extract_member_from_tarball(
        archive_path,
        member_rel_path=Path("DifferentProject/FooAristotleProof.lean"),
        destination=destination,
    )

    assert saved == destination
    assert destination.read_text() == "-- solved proof"


def test_extract_member_from_tarball_uses_only_lean_file_when_unambiguous(tmp_path):
    archive_path = tmp_path / "result.tar.gz"
    source_dir = tmp_path / "src"
    source_dir.mkdir()
    target = source_dir / "Main.lean"
    target.write_text("-- only lean file")
    (source_dir / "README.md").write_text("readme")

    with tarfile.open(archive_path, "w:gz") as archive:
        archive.add(target, arcname="RequestProject/Main.lean")
        archive.add(source_dir / "README.md", arcname="RequestProject/README.md")

    destination = tmp_path / "out" / "FooAristotleProof.lean"
    saved = _extract_member_from_tarball(
        archive_path,
        member_rel_path=Path("RequestProject/FooAristotleProof.lean"),
        destination=destination,
    )

    assert saved == destination
    assert destination.read_text() == "-- only lean file"


def _fake_async(result):
    async def inner(*args, **kwargs):
        return result

    return inner
