import base64
import json
import pickle
import sqlite3
import sys
from pathlib import Path

from cli import run_workflows


def _encode_payload(value):
    return base64.b64encode(pickle.dumps(value)).decode("ascii")


def _init_workflow_db(db_path: Path) -> None:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(db_path)
    conn.executescript(
        """
        CREATE TABLE workflow_status (
            workflow_uuid TEXT PRIMARY KEY,
            status TEXT,
            name TEXT,
            authenticated_user TEXT,
            assumed_role TEXT,
            authenticated_roles TEXT,
            request TEXT,
            output TEXT,
            error TEXT,
            executor_id TEXT,
            created_at INTEGER,
            updated_at INTEGER,
            application_version TEXT,
            application_id TEXT,
            class_name TEXT,
            config_name TEXT,
            recovery_attempts INTEGER,
            queue_name TEXT,
            workflow_timeout_ms INTEGER,
            workflow_deadline_epoch_ms INTEGER,
            inputs TEXT,
            started_at_epoch_ms INTEGER,
            deduplication_id TEXT,
            priority INTEGER,
            queue_partition_key TEXT,
            forked_from TEXT,
            owner_xid TEXT
        );
        CREATE TABLE operation_outputs (
            workflow_uuid TEXT NOT NULL,
            function_id INTEGER NOT NULL,
            function_name TEXT NOT NULL DEFAULT '',
            output TEXT,
            error TEXT,
            child_workflow_id TEXT,
            started_at_epoch_ms BIGINT,
            completed_at_epoch_ms BIGINT,
            PRIMARY KEY (workflow_uuid, function_id)
        );
        CREATE TABLE workflow_events (
            workflow_uuid TEXT NOT NULL,
            key TEXT NOT NULL,
            value TEXT NOT NULL,
            PRIMARY KEY (workflow_uuid, key)
        );
        """
    )

    conn.execute(
        """
        INSERT INTO workflow_status (
            workflow_uuid, status, name, output, error, executor_id, created_at, updated_at,
            class_name, config_name, recovery_attempts, queue_name, inputs, forked_from
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            "parent-workflow",
            "ERROR",
            "run_pipeline",
            _encode_payload({"done": False}),
            _encode_payload(RuntimeError("boom")),
            "pipeline-parent",
            1_700_000_000_000,
            1_700_000_001_000,
            "PipelineRunner",
            "PipelineRunner",
            2,
            "default",
            _encode_payload({"arg": 1}),
            None,
        ),
    )
    conn.execute(
        """
        INSERT INTO workflow_status (
            workflow_uuid, status, name, output, error, executor_id, created_at, updated_at,
            class_name, config_name, recovery_attempts, queue_name, inputs, forked_from
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            "child-workflow",
            "PENDING",
            "ProverV2Agent.prove",
            None,
            None,
            "pipeline-child",
            1_700_000_002_000,
            1_700_000_002_000,
            "ProverV2Agent",
            "ProverV2Agent",
            0,
            "default",
            _encode_payload({"goal": "x"}),
            None,
        ),
    )
    conn.execute(
        """
        INSERT INTO operation_outputs (
            workflow_uuid, function_id, function_name, output, error, child_workflow_id,
            started_at_epoch_ms, completed_at_epoch_ms
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            "parent-workflow",
            1,
            "run_child",
            None,
            None,
            "child-workflow",
            1_700_000_000_100,
            None,
        ),
    )
    conn.execute(
        """
        INSERT INTO operation_outputs (
            workflow_uuid, function_id, function_name, output, error, child_workflow_id,
            started_at_epoch_ms, completed_at_epoch_ms
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            "parent-workflow",
            2,
            "finalize",
            _encode_payload({"ok": True}),
            None,
            None,
            1_700_000_000_200,
            1_700_000_000_300,
        ),
    )
    conn.commit()
    conn.close()


def test_run_workflows_list_supports_regex_after_subcommand(monkeypatch, tmp_path, capsys):
    _init_workflow_db(tmp_path / ".lloom" / "db" / "lloom_pipeline.sqlite")
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "lloom-agent",
            "workflows",
            "list",
            "--project",
            str(tmp_path),
            "--regex",
            "child",
        ],
    )

    run_workflows()

    output = capsys.readouterr().out
    assert "child-workflow" in output
    assert "parent-workflow" not in output


def test_run_workflows_show_and_step_json_decode_payloads(monkeypatch, tmp_path, capsys):
    _init_workflow_db(tmp_path / ".lloom" / "db" / "lloom_pipeline.sqlite")

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "lloom-agent",
            "workflows",
            "show",
            "--project",
            str(tmp_path),
            "--json",
            "parent-workflow",
        ],
    )
    run_workflows()
    show_output = json.loads(capsys.readouterr().out)
    assert show_output["summary"]["db_name"] == "pipeline"
    assert show_output["inputs"] == {"arg": 1}
    assert show_output["steps"][0]["child_workflow_id"] == "child-workflow"
    assert show_output["steps"][0]["child_status"] == "PENDING"

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "lloom-agent",
            "workflows",
            "step",
            "--project",
            str(tmp_path),
            "--json",
            "parent-workflow",
            "2",
        ],
    )
    run_workflows()
    step_output = json.loads(capsys.readouterr().out)
    assert step_output["function_name"] == "finalize"
    assert step_output["output"] == {"ok": True}
    assert step_output["child_workflow_id"] is None
