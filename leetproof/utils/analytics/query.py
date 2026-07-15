"""Read-only analytics query helpers."""

from __future__ import annotations

from dataclasses import MISSING, dataclass, fields, is_dataclass
from enum import Enum
import importlib
import inspect
import json
import sqlite3
import types as pytypes
from typing import Any, Generic, Protocol, TypeVar, Union, get_args, get_origin, get_type_hints

from .common import JSONObject, JSONValue, to_json_value


TPayload = TypeVar("TPayload")

QUERY_OPERATION_MODULES = (
    "utils.analytics.general",
    "utils.analytics.spec_generation",
    "utils.analytics.velvet_programmer",
    "utils.analytics.velvet_invariant_inferrer",
    "utils.analytics.lean_synth_and_verify",
)


@dataclass(frozen=True)
class AnalyticsQueryRow(Generic[TPayload]):
    """One analytics query result row with typed payload plus row metadata."""

    session_name: str
    scope: str
    attempt_no: int
    key: str
    payload: TPayload
    text_content: str | None = None


class ReadonlyQueryStore(Protocol):
    """Minimal store interface required for analytics queries."""

    def ensure_schema(self) -> None: ...
    def _connect(self) -> sqlite3.Connection: ...


@dataclass(frozen=True)
class QueryOperationInfo:
    """Metadata for one exposed analytics query operation."""

    name: str
    module: str
    function: str
    required_parameters: list[str]
    optional_parameters: list[str]
    doc: str | None = None


def strip_leading_sql_comments(sql: str) -> str:
    """Remove leading whitespace and SQL comments for lightweight validation."""
    remaining = sql
    while True:
        stripped = remaining.lstrip()
        if stripped.startswith("--"):
            newline = stripped.find("\n")
            if newline == -1:
                return ""
            remaining = stripped[newline + 1 :]
            continue
        if stripped.startswith("/*"):
            end = stripped.find("*/")
            if end == -1:
                raise ValueError("Unterminated SQL block comment")
            remaining = stripped[end + 2 :]
            continue
        return stripped


def validate_readonly_query(sql: str) -> None:
    """Accept only read-only query entrypoint statements."""
    stripped = strip_leading_sql_comments(sql)
    upper = stripped.upper()
    if not (upper.startswith("SELECT") or upper.startswith("WITH")):
        raise ValueError("Only SELECT/WITH queries are allowed")


def decode_query_value(column: str, value: object) -> JSONValue:
    """Best-effort conversion of SQLite values to JSON-friendly output."""
    if value is None or isinstance(value, (str, int, float, bool)):
        if isinstance(value, str) and column.endswith("_json"):
            try:
                decoded = json.loads(value)
                return to_json_value(decoded)
            except json.JSONDecodeError:
                return value
        return value
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def execute_readonly_query(store: ReadonlyQueryStore, sql: str) -> list[JSONObject]:
    """Run a read-only query against the analytics SQLite store."""
    validate_readonly_query(sql)
    store.ensure_schema()
    with store._connect() as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(sql).fetchall()
    return [{key: decode_query_value(key, row[key]) for key in row.keys()} for row in rows]


def _deserialize_value(value: object, target_type: Any) -> Any:
    if target_type is Any or target_type is object:
        return value

    origin = get_origin(target_type)
    if origin in (list,):
        (item_type,) = get_args(target_type) or (Any,)
        if not isinstance(value, list):
            raise TypeError(f"Expected list for {target_type!r}, got {type(value)!r}")
        return [_deserialize_value(item, item_type) for item in value]

    if origin in (dict,):
        args = get_args(target_type)
        value_type = args[1] if len(args) == 2 else Any
        if not isinstance(value, dict):
            raise TypeError(f"Expected dict for {target_type!r}, got {type(value)!r}")
        return {str(key): _deserialize_value(item, value_type) for key, item in value.items()}

    if origin in (pytypes.UnionType, Union):
        args = get_args(target_type)
        if value is None:
            if type(None) in args:
                return None
            raise TypeError(f"None is not valid for {target_type!r}")
        non_none_args = [arg for arg in args if arg is not type(None)]
        last_error: Exception | None = None
        for arg in non_none_args:
            try:
                return _deserialize_value(value, arg)
            except Exception as exc:  # pragma: no cover - only hit on mismatched unions
                last_error = exc
        raise TypeError(f"Could not deserialize {value!r} as {target_type!r}") from last_error

    if isinstance(target_type, type) and issubclass(target_type, Enum):
        return target_type(value)

    if isinstance(target_type, type) and is_dataclass(target_type):
        if not isinstance(value, dict):
            raise TypeError(f"Expected dict payload for {target_type.__name__}, got {type(value)!r}")
        kwargs: dict[str, Any] = {}
        type_hints = get_type_hints(target_type)
        for field_info in fields(target_type):
            field_type = type_hints.get(field_info.name, field_info.type)
            if field_info.name in value:
                kwargs[field_info.name] = _deserialize_value(value[field_info.name], field_type)
            elif field_info.default is not MISSING or field_info.default_factory is not MISSING:
                continue
            else:
                raise TypeError(
                    f"Missing required field {field_info.name!r} for {target_type.__name__}"
                )
        return target_type(**kwargs)

    if target_type in (str, int, float, bool):
        if not isinstance(value, target_type):
            raise TypeError(f"Expected {target_type.__name__}, got {type(value)!r}")
        return value

    return value


def deserialize_payload(payload: JSONObject, payload_type: type[TPayload]) -> TPayload:
    """Deserialize one JSON payload into a typed analytics payload object."""
    return _deserialize_value(payload, payload_type)


def query_records_by_key(
    store: ReadonlyQueryStore,
    *,
    session_name: str,
    key: str,
    payload_type: type[TPayload],
    scope: str | None = None,
) -> list[AnalyticsQueryRow[TPayload]]:
    """Query rows for one exact key within a session and deserialize their payloads."""
    store.ensure_schema()
    sql = """
        SELECT session_name, scope, attempt_no, key, payload_json, text_content
        FROM attempt_records
        WHERE session_name = ? AND key = ?
    """
    params: list[object] = [session_name, key]
    if scope is not None:
        sql += " AND scope = ?"
        params.append(scope)
    sql += " ORDER BY scope, attempt_no"

    with store._connect() as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(sql, params).fetchall()

    result: list[AnalyticsQueryRow[TPayload]] = []
    for row in rows:
        payload_obj = json.loads(row["payload_json"])
        if not isinstance(payload_obj, dict):
            raise TypeError(f"Expected JSON object payload for key {key!r}")
        result.append(
            AnalyticsQueryRow(
                session_name=str(row["session_name"]),
                scope=str(row["scope"]),
                attempt_no=int(row["attempt_no"]),
                key=str(row["key"]),
                payload=deserialize_payload(payload_obj, payload_type),
                text_content=(
                    None if row["text_content"] is None else str(row["text_content"])
                ),
            )
        )
    return result


def _get_query_operation_registry() -> dict[str, pytypes.FunctionType]:
    registry: dict[str, pytypes.FunctionType] = {}
    for module_name in QUERY_OPERATION_MODULES:
        module = importlib.import_module(module_name)
        short_module_name = module_name.rsplit(".", 1)[-1]
        exported = getattr(module, "QUERY_OPERATIONS", None)
        if not isinstance(exported, dict):
            raise ValueError(f"Analytics module {module_name} must define QUERY_OPERATIONS")
        for operation_name, func in exported.items():
            if not isinstance(operation_name, str):
                raise TypeError(f"Invalid analytics operation name in {module_name}: {operation_name!r}")
            if not inspect.isfunction(func):
                raise TypeError(
                    f"Analytics operation {module_name}.{operation_name} must be a function"
                )
            registry[f"{short_module_name}.{operation_name}"] = func
    return registry


def _resolve_query_operation(operation: str) -> tuple[str, pytypes.FunctionType]:
    registry = _get_query_operation_registry()
    if operation in registry:
        return operation, registry[operation]

    matches = [
        (name, func)
        for name, func in registry.items()
        if name.rsplit(".", 1)[-1] == operation
    ]
    if len(matches) == 1:
        return matches[0]
    if not matches:
        available = ", ".join(sorted(registry))
        raise ValueError(f"Unknown analytics query operation {operation!r}. Available: {available}")
    candidates = ", ".join(sorted(name for name, _ in matches))
    raise ValueError(
        f"Ambiguous analytics query operation {operation!r}. Use one of: {candidates}"
    )


def list_query_operations() -> list[QueryOperationInfo]:
    """Return metadata for all exposed typed analytics query operations."""
    result: list[QueryOperationInfo] = []
    for name, func in sorted(_get_query_operation_registry().items()):
        signature = inspect.signature(func)
        required_parameters: list[str] = []
        optional_parameters: list[str] = []
        for parameter in signature.parameters.values():
            if parameter.kind not in (
                inspect.Parameter.POSITIONAL_OR_KEYWORD,
                inspect.Parameter.KEYWORD_ONLY,
            ):
                continue
            if parameter.default is inspect.Parameter.empty:
                required_parameters.append(parameter.name)
            else:
                optional_parameters.append(parameter.name)
        result.append(
            QueryOperationInfo(
                name=name,
                module=func.__module__,
                function=func.__name__,
                required_parameters=required_parameters,
                optional_parameters=optional_parameters,
                doc=inspect.getdoc(func),
            )
        )
    return result


def execute_query_operation(
    operation: str,
    input_data: JSONObject | None = None,
) -> JSONValue:
    """Execute one exposed typed analytics query operation and return JSON-ready output."""
    resolved_name, func = _resolve_query_operation(operation)
    del resolved_name
    kwargs = {} if input_data is None else dict(input_data)
    signature = inspect.signature(func)
    try:
        bound = signature.bind(**kwargs)
    except TypeError as exc:
        raise ValueError(f"Invalid input for analytics query operation {operation!r}: {exc}") from exc
    result = func(*bound.args, **bound.kwargs)
    return to_json_value(result)


def query(sql: str) -> list[JSONObject]:
    """Execute a read-only analytics query using the shared store."""
    from .store import get_analytics_store

    return execute_readonly_query(get_analytics_store(), sql)

