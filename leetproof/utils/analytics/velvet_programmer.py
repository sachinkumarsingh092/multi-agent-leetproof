"""Typed analytics helpers for ``velvet_programmer``."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from agents.agent_state import JudgeVerdict, PBTStatus

from .query import AnalyticsQueryRow, query_records_by_key
from .store import ATTEMPT_META_KEY, AttemptLog, AttemptRecord, get_analytics_store


DEFAULT_SCOPE = "velvet_programmer"
TYPECHECK_SUMMARY_KEY = "summary.typecheck"
JUDGE_KEY = "judge.velvet_programmer"


class AttemptOutcome(str, Enum):
    """Final attempt outcomes emitted by ``velvet_programmer``."""

    BUILD_FAILURE = "build_failure"
    PBT_FAILURE = "pbt_failure"
    ASSERTION_FAILURE = "assertion_failure"
    JUDGE_PASS = "judge_pass"
    JUDGE_FAIL = "judge_fail"


@dataclass(frozen=True)
class AttemptMeta:
    """Typed ``attempt.meta`` payload for programmer attempts."""

    final_outcome: AttemptOutcome
    file_path: str = ""
    reasoning_level: str | None = None
    error_message: str | None = None


@dataclass(frozen=True)
class TypecheckSummary:
    """Typed ``summary.typecheck`` payload for programmer attempts."""

    build_passed: bool
    pbt_failure: bool
    assertion_failure: bool
    program: str
    impl_section: str
    pbt_status: PBTStatus | None = None
    pbt_failure_message: str | None = None


@dataclass(frozen=True)
class JudgeResult:
    """Typed ``judge.velvet_programmer`` payload."""

    verdict: JudgeVerdict
    reasoning: str
    program: str


def write_typecheck_summary(
    attempt_log: AttemptLog,
    payload: TypecheckSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the programmer typecheck summary for one attempt."""
    return attempt_log.put(TYPECHECK_SUMMARY_KEY, payload, text=text)

def write_judge_result(
    attempt_log: AttemptLog,
    payload: JudgeResult,
) -> AttemptRecord:
    """Write the programmer judge result for one attempt."""
    return attempt_log.put(JUDGE_KEY, payload)


def write_attempt_meta(
    attempt_log: AttemptLog,
    payload: AttemptMeta,
) -> AttemptRecord:
    """Write the typed programmer ``attempt.meta`` row for one attempt."""
    return attempt_log.put(ATTEMPT_META_KEY, payload)


def query_typecheck_summaries(session_name: str) -> list[AnalyticsQueryRow[TypecheckSummary]]:
    """Query all programmer ``summary.typecheck`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=TYPECHECK_SUMMARY_KEY,
        payload_type=TypecheckSummary,
    )



def query_judge_results(session_name: str) -> list[AnalyticsQueryRow[JudgeResult]]:
    """Query all programmer judge rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=JUDGE_KEY,
        payload_type=JudgeResult,
    )



def query_attempt_meta(session_name: str) -> list[AnalyticsQueryRow[AttemptMeta]]:
    """Query all programmer ``attempt.meta`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=ATTEMPT_META_KEY,
        payload_type=AttemptMeta,
    )



QUERY_OPERATIONS = {
    "query_typecheck_summaries": query_typecheck_summaries,
    "query_judge_results": query_judge_results,
    "query_attempt_meta": query_attempt_meta,
}

