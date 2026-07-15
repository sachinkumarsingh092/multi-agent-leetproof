"""General analytics record query helpers."""

from __future__ import annotations

from .store import AttemptRecord, get_analytics_store


def query_records(
    session_name: str,
    scope: str | None = None,
    attempt_no: int | None = None,
    key: str | None = None,
) -> list[AttemptRecord]:
    """Query analytics rows for a session with optional scope/attempt/key filters."""
    return get_analytics_store().fetch_records(
        session_name=session_name,
        scope=scope,
        attempt_no=attempt_no,
        key=key,
    )


QUERY_OPERATIONS = {
    "query_records": query_records,
}
