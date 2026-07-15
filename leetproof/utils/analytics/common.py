"""Shared analytics payloads and JSON serialization helpers."""

from __future__ import annotations

from dataclasses import Field, asdict, dataclass, field, is_dataclass
from enum import Enum
from typing import Any, ClassVar, Protocol, TypeAlias


JSONScalar: TypeAlias = str | int | float | bool | None
JSONValue: TypeAlias = JSONScalar | list["JSONValue"] | dict[str, "JSONValue"]
JSONObject: TypeAlias = dict[str, JSONValue]


class CheckStatus(str, Enum):
    """Common status values for typed check payloads."""

    PASS = "PASS"
    FAIL = "FAIL"
    SKIP = "SKIP"
    PENDING = "PENDING"


@dataclass(frozen=True)
class AttemptMetaPayload:
    """Generic payload shape for ``attempt.meta`` rows."""

    final_outcome: str | Enum
    file_path: str
    reasoning_level: str | None = None
    error_message: str | None = None


@dataclass(frozen=True)
class CheckPayload:
    """Convenience payload shape for ``check.*`` rows."""

    status: CheckStatus | str
    code: str | None = None
    message: str | None = None
    details: JSONObject = field(default_factory=dict)


@dataclass(frozen=True)
class ReviewPayload:
    """Convenience payload shape for ``review.*`` / ``judge.*`` rows."""

    verdict: str
    score: int | None = None
    labels: list[str] = field(default_factory=list)
    short_reason: str | None = None
    details: JSONObject = field(default_factory=dict)


@dataclass(frozen=True)
class EmptyPayload:
    """Marker payload for text-only records such as snapshots."""


class DataclassPayload(Protocol):
    """Structural type for dataclass instances accepted as analytics payloads."""

    __dataclass_fields__: ClassVar[dict[str, Field[object]]]


PayloadInput: TypeAlias = JSONObject | DataclassPayload


def to_json_value(value: object) -> JSONValue:
    """Convert supported Python values into JSON-compatible analytics values."""
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Enum):
        return value.value
    if is_dataclass(value):
        return to_json_value(asdict(value))
    if isinstance(value, dict):
        return {str(key): to_json_value(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [to_json_value(item) for item in value]
    raise TypeError(f"Unsupported analytics payload value: {type(value)!r}")


def normalize_payload(payload: PayloadInput | None = None) -> JSONObject:
    """Normalize supported payload inputs into a JSON object."""
    if payload is None:
        return {}
    normalized = to_json_value(payload)
    if not isinstance(normalized, dict):
        raise TypeError("Analytics payload must serialize to a JSON object")
    return normalized

