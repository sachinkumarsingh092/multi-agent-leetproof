from __future__ import annotations

from dataclasses import dataclass
from typing import Awaitable, Optional, Protocol, TypeVar, Generic

from providers import ReasoningLevel

T = TypeVar("T")
F = TypeVar("F")


@dataclass(frozen=True)
class AttemptContext:
    """Context for a single retry attempt."""

    attempt_index: int
    max_attempts: int


@dataclass
class AttemptOutcome(Generic[T, F]):
    """Outcome of a single attempt.

    success indicates whether the attempt achieved the goal.
    value is the successful result (or last result when failed).
    failure carries updated feedback for the next attempt.
    """

    success: bool
    value: T | None = None
    failure: F | None = None


class EscalationPolicy(Protocol):
    def __call__(self, context: AttemptContext) -> ReasoningLevel | None: ...


class AttemptFn(Protocol[T, F]):
    async def __call__(
        self,
        context: AttemptContext,
        prev_failure: F,
        reasoning_level: ReasoningLevel | None,
    ) -> AttemptOutcome[T, F]: ...


class FeedbackFactory(Protocol[F]):
    def __call__(self) -> F: ...


async def run_with_escalation(
    *,
    max_attempts: int,
    escalation: EscalationPolicy,
    attempt: AttemptFn[T, F],
    feedback_factory: FeedbackFactory[F],
    ) -> AttemptOutcome[T, F]:
    """Run attempts with escalation and optional feedback propagation.

    Args:
        max_attempts: Maximum number of attempts (must be >= 1).
        escalation: Function that maps AttemptContext to ReasoningLevel or None.
        attempt: Async attempt function invoked with context, previous failure, reasoning.
        feedback_factory: Factory for the failure object passed across attempts.

    Returns:
        The first successful outcome, or the last failure outcome.
    """
    if max_attempts < 1:
        raise ValueError("max_attempts must be >= 1")

    prev_failure = feedback_factory()
    last_outcome: Optional[AttemptOutcome[T, F]] = None

    for attempt_index in range(max_attempts):
        context = AttemptContext(
            attempt_index=attempt_index,
            max_attempts=max_attempts,
        )
        reasoning_level = escalation(context)
        outcome = await attempt(context, prev_failure, reasoning_level)
        last_outcome = outcome

        if outcome.success:
            return outcome

        if outcome.failure is not None:
            prev_failure = outcome.failure

    assert last_outcome is not None
    return last_outcome
