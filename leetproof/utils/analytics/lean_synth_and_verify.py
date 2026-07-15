"""Typed analytics helpers for ``lean_synth_and_verify``."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from agents.agent_state import JudgeVerdict, PBTStatus

from .query import AnalyticsQueryRow, query_records_by_key
from .store import ATTEMPT_META_KEY, AttemptLog, AttemptRecord, get_analytics_store


DEFAULT_SCOPE = "lean_synth_and_verify"
TYPECHECK_SUMMARY_KEY = "summary.typecheck"
JUDGE_KEY = "judge.lean_synth_and_verify"
PROOF_SUMMARY_KEY = "summary.proof"


class AttemptOutcome(str, Enum):
    """Final attempt outcomes emitted by ``lean_synth_and_verify``."""

    VALIDATION_FAILURE = "validation_failure"
    BUILD_FAILURE = "build_failure"
    PBT_FAILURE = "pbt_failure"
    JUDGE_FAIL = "judge_fail"
    SYNTHESIS_EXHAUSTED = "synthesis_exhausted"
    JUDGE_RETRY_LIMIT_EXCEEDED = "judge_retry_limit_exceeded"
    PROOF_PREPARATION_FAILURE = "proof_preparation_failure"
    PROOF_PROVEN = "proof_proven"
    PROOF_PARTIAL = "proof_partial"
    PROOF_FAILED = "proof_failed"
    FINAL_BUILD_FAILURE = "final_build_failure"


class ProofStatus(str, Enum):
    """High-level proof status for one lean-synth attempt."""

    PREPARATION_FAILED = "preparation_failed"
    PROVEN = "proven"
    PARTIAL = "partial"
    FAILED = "failed"


@dataclass(frozen=True)
class AttemptMeta:
    """Typed ``attempt.meta`` payload for lean synth attempts."""

    final_outcome: AttemptOutcome
    file_path: str = ""
    reasoning_level: str | None = None
    error_message: str | None = None


@dataclass(frozen=True)
class TypecheckSummary:
    """Typed ``summary.typecheck`` payload for lean synth attempts."""

    validation_passed: bool
    build_passed: bool
    pbt_failure: bool
    program: str
    impl_section: str
    pbt_status: PBTStatus | None = None
    pbt_failure_message: str | None = None


@dataclass(frozen=True)
class JudgeResult:
    """Typed ``judge.lean_synth_and_verify`` payload."""

    verdict: JudgeVerdict
    reasoning: str
    program: str


@dataclass(frozen=True)
class ProofSummary:
    """Typed ``summary.proof`` payload for lean synth attempts."""

    status: ProofStatus
    has_sorry: bool
    final_build_passed: bool
    program: str
    error_message: str | None = None


def write_typecheck_summary(
    attempt_log: AttemptLog,
    payload: TypecheckSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the lean synth typecheck summary for one attempt."""
    return attempt_log.put(TYPECHECK_SUMMARY_KEY, payload, text=text)



def write_judge_result(
    attempt_log: AttemptLog,
    payload: JudgeResult,
) -> AttemptRecord:
    """Write the lean synth judge result for one attempt."""
    return attempt_log.put(JUDGE_KEY, payload)



def write_proof_summary(
    attempt_log: AttemptLog,
    payload: ProofSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the lean synth proof summary for one attempt."""
    return attempt_log.put(PROOF_SUMMARY_KEY, payload, text=text)



def write_attempt_meta(
    attempt_log: AttemptLog,
    payload: AttemptMeta,
) -> AttemptRecord:
    """Write the typed lean synth ``attempt.meta`` row for one attempt."""
    return attempt_log.put(ATTEMPT_META_KEY, payload)



def query_typecheck_summaries(session_name: str) -> list[AnalyticsQueryRow[TypecheckSummary]]:
    """Query all lean synth ``summary.typecheck`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=TYPECHECK_SUMMARY_KEY,
        payload_type=TypecheckSummary,
    )



def query_judge_results(session_name: str) -> list[AnalyticsQueryRow[JudgeResult]]:
    """Query all lean synth judge rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=JUDGE_KEY,
        payload_type=JudgeResult,
    )



def query_proof_summaries(session_name: str) -> list[AnalyticsQueryRow[ProofSummary]]:
    """Query all lean synth ``summary.proof`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=PROOF_SUMMARY_KEY,
        payload_type=ProofSummary,
    )



def query_attempt_meta(session_name: str) -> list[AnalyticsQueryRow[AttemptMeta]]:
    """Query all lean synth ``attempt.meta`` rows for one session."""
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
    "query_proof_summaries": query_proof_summaries,
    "query_attempt_meta": query_attempt_meta,
}
