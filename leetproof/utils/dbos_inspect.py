"""Helpers for inspecting DBOS workflow state stored in SQLite."""

from __future__ import annotations

import base64
import binascii
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path
import pickle
import pprint
import re
import sqlite3
from typing import Any

from config.constants import DB_DIR


@dataclass(frozen=True)
class WorkflowSummary:
    """Summary row for one workflow."""

    db_name: str
    db_path: str
    workflow_uuid: str
    status: str | None
    name: str | None
    class_name: str | None
    config_name: str | None
    created_at_ms: int | None
    updated_at_ms: int | None
    recovery_attempts: int | None
    forked_from: str | None
    queue_name: str | None
    executor_id: str | None


@dataclass(frozen=True)
class StepSummary:
    """Summary row for one workflow step."""

    workflow_uuid: str
    function_id: int
    function_name: str
    child_workflow_id: str | None
    child_status: str | None
    started_at_epoch_ms: int | None
    completed_at_epoch_ms: int | None
    output: Any
    error: Any


@dataclass(frozen=True)
class WorkflowDetail:
    """Full detail for one workflow."""

    summary: WorkflowSummary
    inputs: Any
    output: Any
    error: Any
    steps: list[StepSummary]


@dataclass(frozen=True)
class StepDetail:
    """Full detail for one step."""

    db_name: str
    db_path: str
    workflow_uuid: str
    function_id: int
    function_name: str
    child_workflow_id: str | None
    child_status: str | None
    started_at_epoch_ms: int | None
    completed_at_epoch_ms: int | None
    output: Any
    error: Any


def _connect(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    return conn


def _has_workflow_schema(conn: sqlite3.Connection) -> bool:
    rows = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name IN ('workflow_status', 'operation_outputs')"
    ).fetchall()
    return len(rows) == 2


def _db_name_from_path(path: Path) -> str:
    name = path.stem
    if name.startswith("lloom_"):
        return name[len("lloom_") :]
    return name


def discover_workflow_dbs(project_dir: str | Path, selectors: list[str] | None = None) -> list[Path]:
    """Discover DBOS SQLite databases in a project directory."""

    db_root = Path(project_dir) / DB_DIR
    if not db_root.is_dir():
        raise ValueError(f"DB directory not found: {db_root}")

    db_paths = sorted(path for path in db_root.glob("*.sqlite") if path.is_file())
    workflow_dbs: list[Path] = []
    for db_path in db_paths:
        with _connect(db_path) as conn:
            if _has_workflow_schema(conn):
                workflow_dbs.append(db_path)

    if not selectors:
        return workflow_dbs

    resolved: list[Path] = []
    unresolved: list[str] = []
    by_filename = {path.name: path for path in workflow_dbs}
    by_stem = {path.stem: path for path in workflow_dbs}
    by_short = {_db_name_from_path(path): path for path in workflow_dbs}

    for selector in selectors:
        candidate = Path(selector)
        if candidate.is_file():
            resolved.append(candidate)
            continue

        match = (
            by_filename.get(selector)
            or by_stem.get(selector)
            or by_short.get(selector)
            or by_filename.get(f"{selector}.sqlite")
            or by_filename.get(f"lloom_{selector}.sqlite")
        )
        if match is None:
            unresolved.append(selector)
        else:
            resolved.append(match)

    if unresolved:
        available = ", ".join(sorted(_db_name_from_path(path) for path in workflow_dbs))
        missing = ", ".join(unresolved)
        raise ValueError(f"Unknown workflow DB selector(s): {missing}. Available: {available}")

    deduped: list[Path] = []
    seen: set[Path] = set()
    for path in resolved:
        if path not in seen:
            seen.add(path)
            deduped.append(path)
    return deduped


def _decode_payload(value: Any) -> Any:
    if value is None:
        return None
    if isinstance(value, bytes):
        try:
            return pickle.loads(value)
        except Exception:
            return value.decode("utf-8", errors="replace")
    if not isinstance(value, str):
        return value

    text = value.strip()
    if not text:
        return value

    try:
        raw = base64.b64decode(text, validate=True)
    except (binascii.Error, ValueError):
        return value

    try:
        return pickle.loads(raw)
    except Exception:
        return value


def format_payload(value: Any, *, full: bool = False, max_chars: int = 4000) -> str:
    """Format a decoded payload for terminal output."""

    if value is None:
        return "<none>"
    rendered = pprint.pformat(value, width=100, sort_dicts=False)
    if full or len(rendered) <= max_chars:
        return rendered
    return f"{rendered[:max_chars]}\n... <truncated, use --full to see all>"


def format_timestamp(epoch_ms: int | None) -> str:
    """Format epoch milliseconds as a UTC timestamp."""

    if epoch_ms is None:
        return "-"
    return datetime.fromtimestamp(epoch_ms / 1000, tz=UTC).strftime("%Y-%m-%d %H:%M:%S UTC")


def list_workflows(
    project_dir: str | Path,
    *,
    selectors: list[str] | None = None,
    regex: str | None = None,
    status: str | None = None,
    limit: int = 100,
) -> list[WorkflowSummary]:
    """List workflows across one or more DBOS databases."""

    pattern = re.compile(regex) if regex else None
    rows: list[WorkflowSummary] = []
    for db_path in discover_workflow_dbs(project_dir, selectors):
        with _connect(db_path) as conn:
            query = """
                SELECT workflow_uuid, status, name, class_name, config_name, created_at,
                       updated_at, recovery_attempts, forked_from, queue_name, executor_id
                FROM workflow_status
            """
            params: list[Any] = []
            if status:
                query += " WHERE status = ?"
                params.append(status)
            query += " ORDER BY created_at DESC"
            for row in conn.execute(query, params):
                summary = WorkflowSummary(
                    db_name=_db_name_from_path(db_path),
                    db_path=str(db_path),
                    workflow_uuid=str(row["workflow_uuid"]),
                    status=None if row["status"] is None else str(row["status"]),
                    name=None if row["name"] is None else str(row["name"]),
                    class_name=None if row["class_name"] is None else str(row["class_name"]),
                    config_name=None if row["config_name"] is None else str(row["config_name"]),
                    created_at_ms=None if row["created_at"] is None else int(row["created_at"]),
                    updated_at_ms=None if row["updated_at"] is None else int(row["updated_at"]),
                    recovery_attempts=(
                        None if row["recovery_attempts"] is None else int(row["recovery_attempts"])
                    ),
                    forked_from=None if row["forked_from"] is None else str(row["forked_from"]),
                    queue_name=None if row["queue_name"] is None else str(row["queue_name"]),
                    executor_id=None if row["executor_id"] is None else str(row["executor_id"]),
                )
                if pattern is not None:
                    haystack = " ".join(
                        [
                            summary.workflow_uuid,
                            summary.status or "",
                            summary.name or "",
                            summary.class_name or "",
                            summary.config_name or "",
                            summary.forked_from or "",
                        ]
                    )
                    if pattern.search(haystack) is None:
                        continue
                rows.append(summary)

    rows.sort(key=lambda item: item.created_at_ms or 0, reverse=True)
    return rows[:limit]


def _find_workflow_matches(
    project_dir: str | Path,
    workflow_id: str,
    *,
    selectors: list[str] | None = None,
) -> list[WorkflowSummary]:
    matches: list[WorkflowSummary] = []
    for db_path in discover_workflow_dbs(project_dir, selectors):
        with _connect(db_path) as conn:
            row = conn.execute(
                """
                SELECT workflow_uuid, status, name, class_name, config_name, created_at,
                       updated_at, recovery_attempts, forked_from, queue_name, executor_id
                FROM workflow_status
                WHERE workflow_uuid = ?
                """,
                [workflow_id],
            ).fetchone()
            if row is None:
                continue
            matches.append(
                WorkflowSummary(
                    db_name=_db_name_from_path(db_path),
                    db_path=str(db_path),
                    workflow_uuid=str(row["workflow_uuid"]),
                    status=None if row["status"] is None else str(row["status"]),
                    name=None if row["name"] is None else str(row["name"]),
                    class_name=None if row["class_name"] is None else str(row["class_name"]),
                    config_name=None if row["config_name"] is None else str(row["config_name"]),
                    created_at_ms=None if row["created_at"] is None else int(row["created_at"]),
                    updated_at_ms=None if row["updated_at"] is None else int(row["updated_at"]),
                    recovery_attempts=(
                        None if row["recovery_attempts"] is None else int(row["recovery_attempts"])
                    ),
                    forked_from=None if row["forked_from"] is None else str(row["forked_from"]),
                    queue_name=None if row["queue_name"] is None else str(row["queue_name"]),
                    executor_id=None if row["executor_id"] is None else str(row["executor_id"]),
                )
            )
    return matches


def _require_unique_workflow(
    project_dir: str | Path,
    workflow_id: str,
    *,
    selectors: list[str] | None = None,
) -> WorkflowSummary:
    matches = _find_workflow_matches(project_dir, workflow_id, selectors=selectors)
    if not matches:
        raise ValueError(f"Workflow not found: {workflow_id}")
    if len(matches) > 1:
        db_names = ", ".join(match.db_name for match in matches)
        raise ValueError(
            f"Workflow {workflow_id!r} exists in multiple DBs ({db_names}); use --db to disambiguate"
        )
    return matches[0]


def get_workflow_detail(
    project_dir: str | Path,
    workflow_id: str,
    *,
    selectors: list[str] | None = None,
) -> WorkflowDetail:
    """Load one workflow and its steps."""

    summary = _require_unique_workflow(project_dir, workflow_id, selectors=selectors)
    db_path = Path(summary.db_path)
    with _connect(db_path) as conn:
        row = conn.execute(
            "SELECT inputs, output, error FROM workflow_status WHERE workflow_uuid = ?",
            [workflow_id],
        ).fetchone()
        if row is None:
            raise ValueError(f"Workflow not found: {workflow_id}")

        child_statuses = {
            str(child_row["workflow_uuid"]): (
                None if child_row["status"] is None else str(child_row["status"])
            )
            for child_row in conn.execute(
                """
                SELECT DISTINCT ws.workflow_uuid, ws.status
                FROM workflow_status ws
                JOIN operation_outputs oo ON ws.workflow_uuid = oo.child_workflow_id
                WHERE oo.workflow_uuid = ? AND oo.child_workflow_id IS NOT NULL
                """,
                [workflow_id],
            )
        }

        steps: list[StepSummary] = []
        for step_row in conn.execute(
            """
            SELECT workflow_uuid, function_id, function_name, child_workflow_id,
                   started_at_epoch_ms, completed_at_epoch_ms, output, error
            FROM operation_outputs
            WHERE workflow_uuid = ?
            ORDER BY function_id
            """,
            [workflow_id],
        ):
            child_workflow_id = (
                None
                if step_row["child_workflow_id"] is None
                else str(step_row["child_workflow_id"])
            )
            steps.append(
                StepSummary(
                    workflow_uuid=str(step_row["workflow_uuid"]),
                    function_id=int(step_row["function_id"]),
                    function_name=str(step_row["function_name"]),
                    child_workflow_id=child_workflow_id,
                    child_status=child_statuses.get(child_workflow_id) if child_workflow_id else None,
                    started_at_epoch_ms=(
                        None
                        if step_row["started_at_epoch_ms"] is None
                        else int(step_row["started_at_epoch_ms"])
                    ),
                    completed_at_epoch_ms=(
                        None
                        if step_row["completed_at_epoch_ms"] is None
                        else int(step_row["completed_at_epoch_ms"])
                    ),
                    output=_decode_payload(step_row["output"]),
                    error=_decode_payload(step_row["error"]),
                )
            )

    return WorkflowDetail(
        summary=summary,
        inputs=_decode_payload(row["inputs"]),
        output=_decode_payload(row["output"]),
        error=_decode_payload(row["error"]),
        steps=steps,
    )


def get_step_detail(
    project_dir: str | Path,
    workflow_id: str,
    function_id: int,
    *,
    selectors: list[str] | None = None,
) -> StepDetail:
    """Load one workflow step."""

    summary = _require_unique_workflow(project_dir, workflow_id, selectors=selectors)
    db_path = Path(summary.db_path)
    with _connect(db_path) as conn:
        row = conn.execute(
            """
            SELECT workflow_uuid, function_id, function_name, child_workflow_id,
                   started_at_epoch_ms, completed_at_epoch_ms, output, error
            FROM operation_outputs
            WHERE workflow_uuid = ? AND function_id = ?
            """,
            [workflow_id, function_id],
        ).fetchone()
        if row is None:
            raise ValueError(f"Step {function_id} not found in workflow {workflow_id}")

        child_workflow_id = (
            None if row["child_workflow_id"] is None else str(row["child_workflow_id"])
        )
        child_status = None
        if child_workflow_id:
            child_row = conn.execute(
                "SELECT status FROM workflow_status WHERE workflow_uuid = ?",
                [child_workflow_id],
            ).fetchone()
            if child_row is not None and child_row["status"] is not None:
                child_status = str(child_row["status"])

    return StepDetail(
        db_name=summary.db_name,
        db_path=summary.db_path,
        workflow_uuid=str(row["workflow_uuid"]),
        function_id=int(row["function_id"]),
        function_name=str(row["function_name"]),
        child_workflow_id=child_workflow_id,
        child_status=child_status,
        started_at_epoch_ms=(
            None if row["started_at_epoch_ms"] is None else int(row["started_at_epoch_ms"])
        ),
        completed_at_epoch_ms=(
            None if row["completed_at_epoch_ms"] is None else int(row["completed_at_epoch_ms"])
        ),
        output=_decode_payload(row["output"]),
        error=_decode_payload(row["error"]),
    )


def to_dict(value: Any) -> Any:
    """Convert dataclasses recursively to plain dictionaries."""

    if hasattr(value, "__dataclass_fields__"):
        return {
            key: to_dict(item)
            for key, item in asdict(value).items()
        }
    if isinstance(value, list):
        return [to_dict(item) for item in value]
    if isinstance(value, tuple):
        return [to_dict(item) for item in value]
    if isinstance(value, dict):
        return {str(key): to_dict(item) for key, item in value.items()}
    return value
