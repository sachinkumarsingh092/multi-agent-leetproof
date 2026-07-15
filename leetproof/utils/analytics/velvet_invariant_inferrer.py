"""Typed analytics helpers for ``velvet_invariant_inferrer``."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum

from .query import AnalyticsQueryRow, query_records_by_key
from .store import ATTEMPT_META_KEY, AttemptLog, AttemptRecord, get_analytics_store


DEFAULT_SCOPE = "velvet_invariant_inferrer"
TYPECHECK_SUMMARY_KEY = "summary.typecheck"
CORRECTNESS_SUMMARY_KEY = "summary.correctness"


class AttemptOutcome(str, Enum):
    """Final attempt outcomes emitted by ``velvet_invariant_inferrer``."""

    INVALID_OUTPUT_FILE = "invalid_output_file"
    VALIDATION_FAILED = "validation_failed"
    BUILD_FAILURE = "build_failure"
    PBT_FAILURE = "pbt_failure"
    CORRECTNESS_ISSUES = "correctness_issues"
    CORRECTNESS_INCONCLUSIVE = "correctness_inconclusive"
    JUDGE_PASS = "judge_pass"
    JUDGE_FAIL = "judge_fail"


class CorrectnessVerdict(str, Enum):
    """High-level correctness verdict for invariant checking."""

    OK = "ok"
    ISSUES = "issues"
    INCONCLUSIVE = "inconclusive"


class CorrectnessGoalKind(str, Enum):
    """Kinds of goals checked during invariant correctness analysis."""

    INVARIANT = "invariant"
    NON_INVARIANT = "non_invariant"


@dataclass(frozen=True)
class AttemptMeta:
    """Typed ``attempt.meta`` payload for inferrer attempts."""

    final_outcome: AttemptOutcome
    file_path: str = ""
    reasoning_level: str | None = None
    error_message: str | None = None


@dataclass(frozen=True)
class TypecheckSummary:
    """Typed ``summary.typecheck`` payload for inferrer attempts."""

    validation_passed: bool
    build_passed: bool
    pbt_failure: bool
    program: str
    impl_section: str
    pbt_failure_message: str | None = None


@dataclass(frozen=True)
class LLMGoalResult:
    """Typed per-goal LLM correctness result inside ``summary.correctness``."""

    kind: CorrectnessGoalKind
    goal_id: str
    label: str
    goal_statement: str
    is_provable: bool
    justification: str
    correction_hint: str = ""
    success: bool = True
    error: str | None = None


@dataclass
class CorrectnessSummary:
    """Typed ``summary.correctness`` payload for inferrer attempts."""

    verdict: CorrectnessVerdict = CorrectnessVerdict.OK
    invariant_goal_count: int = 0
    non_invariant_goal_count: int = 0
    extracted_goals_typecheck_passed: bool | None = None
    counterexample_found: bool = False
    automation_discharged_invariant_goals: int = 0
    automation_discharged_non_invariant_goals: int = 0
    llm_results: list[LLMGoalResult] = field(default_factory=list)


def write_typecheck_summary(
    attempt_log: AttemptLog,
    payload: TypecheckSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the inferrer typecheck summary for one attempt."""
    return attempt_log.put(TYPECHECK_SUMMARY_KEY, payload, text=text)


def write_correctness_summary(
    attempt_log: AttemptLog,
    payload: CorrectnessSummary,
    *,
    text: str | None = None,
) -> AttemptRecord:
    """Write the inferrer correctness summary for one attempt."""
    return attempt_log.put(CORRECTNESS_SUMMARY_KEY, payload, text=text)


def write_attempt_meta(
    attempt_log: AttemptLog,
    payload: AttemptMeta,
) -> AttemptRecord:
    """Write the typed inferrer ``attempt.meta`` row for one attempt."""
    return attempt_log.put(ATTEMPT_META_KEY, payload)


def query_typecheck_summaries(session_name: str) -> list[AnalyticsQueryRow[TypecheckSummary]]:
    """Query all inferrer ``summary.typecheck`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=TYPECHECK_SUMMARY_KEY,
        payload_type=TypecheckSummary,
    )



def query_correctness_summaries(session_name: str) -> list[AnalyticsQueryRow[CorrectnessSummary]]:
    """Query all inferrer ``summary.correctness`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=CORRECTNESS_SUMMARY_KEY,
        payload_type=CorrectnessSummary,
    )



def query_attempt_meta(session_name: str) -> list[AnalyticsQueryRow[AttemptMeta]]:
    """Query all inferrer ``attempt.meta`` rows for one session."""
    return query_records_by_key(
        get_analytics_store(),
        session_name=session_name,
        scope=DEFAULT_SCOPE,
        key=ATTEMPT_META_KEY,
        payload_type=AttemptMeta,
    )



QUERY_OPERATIONS = {
    "query_typecheck_summaries": query_typecheck_summaries,
    "query_correctness_summaries": query_correctness_summaries,
    "query_attempt_meta": query_attempt_meta,
}

