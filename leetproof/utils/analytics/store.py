"""SQLite-backed analytics storage for attempt-scoped records."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from functools import lru_cache
import json
import os
from pathlib import Path
import sqlite3

from config.constants import ANALYTICS_DB

from .common import (
    AttemptMetaPayload,
    CheckPayload,
    CheckStatus,
    JSONObject,
    PayloadInput,
    ReviewPayload,
    normalize_payload,
)
from .query import execute_readonly_query


ATTEMPT_META_KEY = "attempt.meta"
SNAPSHOT_PREFIX = "snapshot."
CHECK_PREFIX = "check."
SUMMARY_PREFIX = "summary."
DETAILS_PREFIX = "details."
REVIEW_PREFIX = "review."
JUDGE_PREFIX = "judge."

ANALYTICS_DB_ENV_VAR = "LLOOM_ANALYTICS_DB_PATH"
_analytics_db_override: str | Path | None = None

SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS attempt_records (
    session_name TEXT NOT NULL,
    scope TEXT NOT NULL,
    attempt_no INTEGER NOT NULL,
    key TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    text_content TEXT,
    PRIMARY KEY (session_name, scope, attempt_no, key)
);
"""


@dataclass(frozen=True)
class AttemptRecord:
    """One row in the flattened ``attempt_records`` table."""

    session_name: str
    scope: str
    attempt_no: int
    key: str
    payload: JSONObject = field(default_factory=dict)
    text_content: str | None = None


def current_session_name(default: str = "default") -> str:
    """Resolve the current session name from CLI args.

    Falls back to ``default`` when args are unavailable (e.g. unit tests,
    imports outside the main CLI entrypoint, or parse failures).
    """
    try:
        from args import get_args

        args = get_args()
        session_name = getattr(args, "session_name", None)
        return session_name or default
    except BaseException:
        return default


@lru_cache(maxsize=1)
def get_analytics_store() -> "AnalyticsStore":
    """Return a process-local singleton analytics store."""
    return AnalyticsStore(_resolve_analytics_db_path())


def _resolve_analytics_db_path() -> str | Path:
    """Resolve the analytics DB path from override, env var, or default."""
    if _analytics_db_override is not None:
        return _analytics_db_override
    return os.environ.get(ANALYTICS_DB_ENV_VAR, ANALYTICS_DB)


def set_analytics_db_path(db_path: str | Path | None) -> None:
    """Override the shared analytics DB path for the current process."""
    global _analytics_db_override
    _analytics_db_override = db_path
    get_analytics_store.cache_clear()


def attempt(
    scope: str,
    attempt_no: int,
    *,
    session_name: str | None = None,
) -> "AttemptLog":
    """Bind a logical attempt using the default shared store."""
    return get_analytics_store().attempt(
        scope,
        attempt_no,
        session_name=session_name,
    )


class AnalyticsStore:
    """SQLite-backed store for attempt-scoped analytics rows."""

    def __init__(self, db_path: str | Path = ANALYTICS_DB):
        self.db_path = Path(db_path)
        self._schema_ready = False

    def ensure_schema(self) -> None:
        if self._schema_ready:
            return
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        with self._connect() as conn:
            conn.executescript(SCHEMA_SQL)
        self._schema_ready = True

    def _connect(self) -> sqlite3.Connection:
        return sqlite3.connect(self.db_path)

    def attempt(
        self,
        scope: str,
        attempt_no: int,
        *,
        session_name: str | None = None,
    ) -> AttemptLog:
        """Bind a logical attempt namespace for subsequent writes."""
        return AttemptLog(
            store=self,
            session_name=session_name or current_session_name(),
            scope=scope,
            attempt_no=attempt_no,
        )

    def upsert(self, record: AttemptRecord) -> AttemptRecord:
        """Insert or replace a record for one logical attempt key."""
        self.ensure_schema()
        with self._connect() as conn:
            conn.execute(
                """
                INSERT INTO attempt_records (
                    session_name,
                    scope,
                    attempt_no,
                    key,
                    payload_json,
                    text_content
                ) VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(session_name, scope, attempt_no, key) DO UPDATE SET
                    payload_json = excluded.payload_json,
                    text_content = excluded.text_content
                """,
                (
                    record.session_name,
                    record.scope,
                    record.attempt_no,
                    record.key,
                    json.dumps(record.payload, sort_keys=True),
                    record.text_content,
                ),
            )
        return record

    def fetch_records(
        self,
        *,
        session_name: str | None = None,
        scope: str | None = None,
        attempt_no: int | None = None,
        key: str | None = None,
    ) -> list[AttemptRecord]:
        """Return analytics rows for a session with optional exact-match filters."""
        resolved_session = session_name or current_session_name()
        self.ensure_schema()

        sql = """
            SELECT session_name, scope, attempt_no, key, payload_json, text_content
            FROM attempt_records
            WHERE session_name = ?
        """
        params: list[object] = [resolved_session]
        if scope is not None:
            sql += " AND scope = ?"
            params.append(scope)
        if attempt_no is not None:
            sql += " AND attempt_no = ?"
            params.append(attempt_no)
        if key is not None:
            sql += " AND key = ?"
            params.append(key)
        sql += " ORDER BY scope, attempt_no, key"

        with self._connect() as conn:
            rows = conn.execute(sql, params).fetchall()
        return [
            AttemptRecord(
                session_name=row[0],
                scope=row[1],
                attempt_no=row[2],
                key=row[3],
                payload=json.loads(row[4]),
                text_content=row[5],
            )
            for row in rows
        ]

    def fetch_attempt(
        self,
        scope: str,
        attempt_no: int,
        *,
        session_name: str | None = None,
    ) -> list[AttemptRecord]:
        """Return all stored rows for one logical attempt."""
        return self.fetch_records(
            session_name=session_name,
            scope=scope,
            attempt_no=attempt_no,
        )

    def query(self, sql: str) -> list[JSONObject]:
        """Execute a read-only analytics query and return JSON-ready rows."""
        return execute_readonly_query(self, sql)


@dataclass
class AttemptLog:
    """Small writer bound to one logical attempt namespace."""

    store: AnalyticsStore
    session_name: str
    scope: str
    attempt_no: int

    def put(
        self,
        key: str,
        payload: PayloadInput | None = None,
        *,
        text: str | None = None,
    ) -> AttemptRecord:
        """Write one keyed record for the current attempt."""
        record = AttemptRecord(
            session_name=self.session_name,
            scope=self.scope,
            attempt_no=self.attempt_no,
            key=key,
            payload=normalize_payload(payload),
            text_content=text,
        )
        return self.store.upsert(record)

    def snapshot(
        self,
        name: str,
        text: str,
        payload: PayloadInput | None = None,
    ) -> AttemptRecord:
        """Convenience helper for ``snapshot.*`` records."""
        return self.put(f"{SNAPSHOT_PREFIX}{name}", payload, text=text)

    def check(
        self,
        name: str,
        *,
        status: CheckStatus | str,
        code: str | None = None,
        message: str | None = None,
        details: JSONObject | None = None,
        text: str | None = None,
    ) -> AttemptRecord:
        """Convenience helper for ``check.*`` records."""
        return self.put(
            f"{CHECK_PREFIX}{name}",
            CheckPayload(
                status=status,
                code=code,
                message=message,
                details=details or {},
            ),
            text=text,
        )

    def summary(
        self,
        name: str,
        payload: PayloadInput | None = None,
        *,
        text: str | None = None,
    ) -> AttemptRecord:
        """Convenience helper for ``summary.*`` records."""
        return self.put(f"{SUMMARY_PREFIX}{name}", payload, text=text)

    def details(
        self,
        name: str,
        payload: PayloadInput | None = None,
        *,
        text: str | None = None,
    ) -> AttemptRecord:
        """Convenience helper for ``details.*`` records."""
        return self.put(f"{DETAILS_PREFIX}{name}", payload, text=text)

    def review(
        self,
        name: str,
        *,
        verdict: str,
        score: int | None = None,
        labels: list[str] | None = None,
        short_reason: str | None = None,
        details: JSONObject | None = None,
        text: str | None = None,
        prefix: str = REVIEW_PREFIX,
    ) -> AttemptRecord:
        """Convenience helper for ``review.*`` and ``judge.*`` records."""
        return self.put(
            f"{prefix}{name}",
            ReviewPayload(
                verdict=verdict,
                score=score,
                labels=labels or [],
                short_reason=short_reason,
                details=details or {},
            ),
            text=text,
        )

    def judge(
        self,
        name: str,
        *,
        verdict: str,
        score: int | None = None,
        labels: list[str] | None = None,
        short_reason: str | None = None,
        details: JSONObject | None = None,
        text: str | None = None,
    ) -> AttemptRecord:
        """Convenience helper for ``judge.*`` records."""
        return self.review(
            name,
            verdict=verdict,
            score=score,
            labels=labels,
            short_reason=short_reason,
            details=details,
            text=text,
            prefix=JUDGE_PREFIX,
        )

    def finish(
        self,
        *,
        final_outcome: str | Enum,
        file_path: str,
        reasoning_level: str | None = None,
        error_message: str | None = None,
    ) -> AttemptRecord:
        """Write/update the reserved ``attempt.meta`` row."""
        return self.put(
            ATTEMPT_META_KEY,
            AttemptMetaPayload(
                final_outcome=final_outcome,
                file_path=file_path,
                reasoning_level=reasoning_level,
                error_message=error_message,
            ),
        )
