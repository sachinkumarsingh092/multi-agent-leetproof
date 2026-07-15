"""Typed analytics helpers for ``spec_generation``."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from agents.spec_state import CoachVerdict

from .query import AnalyticsQueryRow, query_records_by_key
from .store import ATTEMPT_META_KEY, AttemptLog, AttemptRecord, get_analytics_store


DEFAULT_SCOPE = "spec_generation"
TYPECHECK_SUMMARY_KEY = "summary.typecheck"
PBT_SUMMARY_KEY = "summary.pbt"
COACH_REVIEW_KEY = "review.spec_coach"


class AttemptOutcome(str, Enum):
    """Final attempt outcomes emitted by ``spec_generation``."""

    TYPECHECK_FAILURE = "typecheck_failure"
    PBT_BUG = "pbt_bug"
    COACH_ACCEPT = "coach_accept"
    COACH_ACCEPT_WITH_MINOR_ISSUES = "coach_accept_with_minor_issues"
    COACH_REJECT = "coach_reject"


class SpecPBTResult(str, Enum):
    """Result of spec property-based testing for one attempt."""

    NO_BUG = "no_bug"
    BUG = "bug"
    PRECOND_BUG = "precond_bug"
    POSTCOND_BUG = "postcond_bug"
    SYNTHESIS_FAILED = "synthesis_failed"


@dataclass(frozen=True)
class AttemptMeta:
    """Typed ``attempt.meta`` payload for spec-generation attempts."""

    final_outcome: AttemptOutcome
    file_path: str = ""
    reasoning_level: str | None = None
    error_message: str | None = None


@dataclass(frozen=True)
class TypecheckSummary:
    """Typed ``summary.typecheck`` payload for spec-generation attempts."""

    build_passed: bool
    has_axiom: bool
    sorry_count: int
    extracted_goals_typecheck_passed: bool | None
    spec: str
    specs_section: str
    impl_section: str
    testcases_section: str


@dataclass(frozen=True)
class PBTSummary:
    """Typed ``summary.pbt`` payload for spec-generation attempts."""

    enabled: bool
    result: SpecPBTResult | None


@dataclass(frozen=True)
class CoachReview:
    """Typed ``review.spec_coach`` payload for spec-generation attempts."""

    verdict: CoachVerdict
    score: int



def write_typecheck_summary(
    attempt_log: AttemptLog,
    payload: TypecheckSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the spec-generation typecheck summary for one attempt."""
    return attempt_log.put(TYPECHECK_SUMMARY_KEY, payload, text=text)



def write_pbt_summary(
    attempt_log: AttemptLog,
    payload: PBTSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the spec-generation PBT summary for one attempt."""
    return attempt_log.put(PBT_SUMMARY_KEY, payload, text=text)



def write_coach_review(
    attempt_log: AttemptLog,
    payload: CoachReview,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the spec-generation coach review for one attempt."""
    return attempt_log.put(COACH_REVIEW_KEY, payload, text=text)



def write_attempt_meta(
    attempt_log: AttemptLog,
    payload: AttemptMeta,
) -> AttemptRecord:
    """Write the typed spec-generation ``attempt.meta`` row for one attempt."""
    return attempt_log.put(ATTEMPT_META_KEY, payload)



def query_typecheck_summaries(session_name: str) -> list[AnalyticsQueryRow[TypecheckSummary]]:
    """Query all spec-generation ``summary.typecheck`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=TYPECHECK_SUMMARY_KEY,
        payload_type=TypecheckSummary,
    )



def query_pbt_summaries(session_name: str) -> list[AnalyticsQueryRow[PBTSummary]]:
    """Query all spec-generation ``summary.pbt`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=PBT_SUMMARY_KEY,
        payload_type=PBTSummary,
    )



def query_coach_reviews(session_name: str) -> list[AnalyticsQueryRow[CoachReview]]:
    """Query all spec-generation ``review.spec_coach`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=COACH_REVIEW_KEY,
        payload_type=CoachReview,
    )



def query_attempt_meta(session_name: str) -> list[AnalyticsQueryRow[AttemptMeta]]:
    """Query all spec-generation ``attempt.meta`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=ATTEMPT_META_KEY,
        payload_type=AttemptMeta,
    )


QUERY_OPERATIONS = {
    "query_typecheck_summaries": query_typecheck_summaries,
    "query_pbt_summaries": query_pbt_summaries,
    "query_coach_reviews": query_coach_reviews,
    "query_attempt_meta": query_attempt_meta,
}
