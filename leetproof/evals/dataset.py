"""
Dataset problem types — dataclass hierarchy with schema metadata.

Each dataset (mbpp, verina, custom) has a subclass of DatasetProblem.
Dispatch is purely on the ``dataset`` key via a registry.

The dataclass fields double as a schema: use ``schema()`` to introspect
field names, descriptions, required/optional, groups, and defaults — useful
for generating JSON test files interactively (see ``gen_batch.py``).

Usage::

    from evals.dataset import parse_test_case, get_schema, available_datasets

    # Parse a raw JSON dict into a typed object
    problem = parse_test_case({"dataset": "mbpp", "id_type": "mbpp_id", "id": 807})
    problem.problem_id   # "mbpp_id_807"
    problem.label        # "MBPP ID807"
    problem.extract(cwd) # writes input file, returns (path, error)
    problem.to_dict()    # round-trips back to JSON dict

    # Introspect schema for UI generation
    get_schema("verina")  # [{name, description, required, type, default, group, ...}, ...]
"""

from __future__ import annotations

import dataclasses
import json
from dataclasses import dataclass, field, fields as dc_fields, replace
from enum import Enum
from pathlib import Path
from typing import Any


# ---------------------------------------------------------------------------
# Schema types
# ---------------------------------------------------------------------------

class FieldType(Enum):
    """Supported schema field types — used for type-appropriate prompting."""
    STR = "str"
    INT = "int"
    BOOL = "bool"

    @classmethod
    def from_annotation(cls, annotation) -> FieldType:
        """Resolve a dataclass field type annotation to a FieldType."""
        raw = annotation if isinstance(annotation, str) else getattr(annotation, "__name__", str(annotation))
        if "bool" in raw:
            return cls.BOOL
        if "int" in raw:
            return cls.INT
        return cls.STR


@dataclass(frozen=True)
class SchemaField:
    """Typed descriptor for a single schema field — returned by ``schema()``."""
    name: str
    description: str
    required: bool
    type: FieldType
    default: Any
    choices: list[str] | None = None
    group: str | None = None
    required_when: dict[str, list] | None = None


# ---------------------------------------------------------------------------
# Schema field helper
# ---------------------------------------------------------------------------

def schema_field(description: str, *, required: bool = True,
                 choices: list[str] | None = None,
                 group: str | None = None,
                 required_when: dict[str, list] | None = None,
                 **kwargs):
    """Dataclass field with schema metadata for introspection.

    Args:
        description: Human-readable description shown in prompts.
        required: Whether the field must be provided.
        choices: Allowed values (for enum-like fields).
        group: Presentation group name (fields with the same group are
               shown together; fields without a group are identity fields).
        required_when: Conditional requirement — a dict mapping field names
                       to lists of values. If any referenced field has one of
                       the listed values, this field becomes required.
                       E.g. ``{"mode": ["pure_lean", "pure_dafny"]}``.
    """
    meta: dict[str, Any] = {"description": description, "required": required}
    if choices is not None:
        meta["choices"] = choices
    if group is not None:
        meta["group"] = group
    if required_when is not None:
        meta["required_when"] = required_when
    return field(metadata=meta, **kwargs)


# ---------------------------------------------------------------------------
# Base class
# ---------------------------------------------------------------------------

@dataclass
class DatasetProblem:
    """Base dataset problem with run-configuration fields common to all datasets."""

    mode: str = schema_field(
        "Synthesis mode", required=False, default="standard",
        choices=["standard", "pure_lean", "pure_dafny"],
        group="Synthesis mode")
    input_file: str | None = schema_field(
        "Path to spec file", required=False, default=None,
        group="Spec file",
        required_when={"mode": ["pure_lean", "pure_dafny"]})
    cwd: str | None = schema_field(
        "Working directory (Lean project path, defaults to --project)",
        required=False, default=None,
        group="Project")
    options: str | None = schema_field(
        "Extra CLI flags for the pipeline", required=False, default=None,
        group="Extra")
    resume: bool = schema_field(
        "Resume from last session", required=False, default=False,
        group="Session")
    session_name: str | None = schema_field(
        "Custom session name", required=False, default=None,
        group="Session")

    def __post_init__(self):
        if self.mode not in ("standard", "pure_lean", "pure_dafny"):
            raise ValueError(f"Invalid mode: '{self.mode}'")
        if self.mode != "standard" and not self.input_file:
            raise ValueError(f"'{self.mode}' mode requires 'input_file' (path to spec file)")

    # -- identity (overridden by subclasses) --------------------------------

    @classmethod
    def dataset_name(cls) -> str:
        """The dataset identifier (e.g. ``"mbpp"``, ``"verina"``, ``"custom"``)."""
        raise NotImplementedError

    @property
    def problem_id(self) -> str:
        """Canonical problem identifier (e.g. ``"mbpp_id_807"``, ``"verina_basic_15"``)."""
        raise NotImplementedError

    @property
    def label(self) -> str:
        """Human-readable label (e.g. ``"MBPP ID807"``, ``"Verina basic 15"``)."""
        raise NotImplementedError

    # -- derived properties -------------------------------------------------

    @property
    def test_key(self) -> str:
        """Canonical key for session naming / pattern matching.

        Appends a mode suffix (``_pure_lean`` or ``_pure_dafny``) so that
        sessions for different modes don't collide.
        """
        key = self.problem_id
        if self.mode != "standard":
            key += f"_{self.mode}"
        return key

    @property
    def base_name(self) -> str:
        """Base name without mode suffixes — used for file naming and glob matching."""
        key = self.test_key
        for suffix in ("_pure_lean", "_pure_dafny"):
            key = key.removesuffix(suffix)
        return key

    # -- extraction ---------------------------------------------------------

    def extract(self, cwd: str) -> tuple[str | None, str]:
        """Extract problem description to an input file.

        Returns ``(relative_path, error_message)``.
        ``relative_path`` is ``None`` on failure, ``error_message`` is ``""`` on success.
        """
        return None, f"No extraction supported for dataset: {self.dataset_name()}"

    # -- serialization ------------------------------------------------------

    def to_dict(self) -> dict:
        """Serialize back to a JSON-compatible dict (for generating test files)."""
        d: dict[str, Any] = {"dataset": self.dataset_name()}
        if self.mode != "standard":
            d["mode"] = self.mode
        if self.input_file is not None:
            d["input_file"] = self.input_file
        if self.cwd is not None:
            d["cwd"] = self.cwd
        if self.options is not None:
            d["options"] = self.options
        if self.resume:
            d["resume"] = True
        if self.session_name is not None:
            d["session_name"] = self.session_name
        return d

    @classmethod
    def from_dict(cls, data: dict) -> DatasetProblem:
        """Parse from a JSON dict. Dispatches to the correct subclass via the registry."""
        ds = data.get("dataset", "custom")
        subcls = _REGISTRY.get(ds, CustomProblem)
        return subcls._from_dict(data)

    @classmethod
    def _from_dict(cls, data: dict) -> DatasetProblem:
        """Subclass-specific parsing. Override in each subclass."""
        raise NotImplementedError

    @staticmethod
    def _base_kwargs(data: dict) -> dict:
        """Extract base-class fields from a raw dict."""
        return {
            "mode": data.get("mode", "standard"),
            "input_file": data.get("input_file"),
            "cwd": data.get("cwd"),
            "options": data.get("options"),
            "resume": bool(data.get("resume", False)),
            "session_name": data.get("session_name"),
        }

    # -- schema introspection -----------------------------------------------

    @classmethod
    def schema(cls) -> list[SchemaField]:
        """Return typed field descriptors for UI / JSON generation.

        Fields without a ``group`` are identity fields (dataset-specific).
        Fields with a ``group`` are run-configuration options.
        """
        result: list[SchemaField] = []
        for f in dc_fields(cls):
            meta = f.metadata
            if "description" not in meta:
                continue
            default = f.default if f.default is not dataclasses.MISSING else None
            result.append(SchemaField(
                name=f.name,
                description=meta["description"],
                required=meta.get("required", True),
                type=FieldType.from_annotation(f.type),
                default=default,
                choices=meta.get("choices"),
                group=meta.get("group"),
                required_when=meta.get("required_when"),
            ))
        return result


# ---------------------------------------------------------------------------
# MBPP
# ---------------------------------------------------------------------------

@dataclass
class MbppProblem(DatasetProblem):
    """MBPP benchmark problem.

    ``id_type`` selects the numbering scheme:
    - ``"position"``: sequential index 1-228
    - ``"mbpp_id"``: original MBPP task ID (e.g. 807)
    """

    id_type: str = schema_field(
        "ID numbering scheme", required=True, default="",
        choices=["position", "mbpp_id"])
    id: int = schema_field(
        "Problem number (position 1-228, or original MBPP task ID)", required=True, default=0)

    def __post_init__(self):
        super().__post_init__()
        if self.id_type not in ("position", "mbpp_id"):
            raise ValueError(f"MbppProblem id_type must be 'position' or 'mbpp_id', got '{self.id_type}'")
        if not self.id:
            raise ValueError("MbppProblem requires 'id'")

    @classmethod
    def dataset_name(cls) -> str:
        return "mbpp"

    @property
    def _use_mbpp_id(self) -> bool:
        return self.id_type == "mbpp_id"

    @property
    def _resolved_mbpp_id(self) -> int | str:
        """Resolve to an MBPP task ID (for human-readable labels)."""
        if self._use_mbpp_id:
            return self.id
        from evals.mbpp import position_to_mbpp_id
        resolved = position_to_mbpp_id(self.id)
        return resolved if resolved is not None else "unknown"

    @property
    def problem_id(self) -> str:
        """Raw identifier used for extraction and output file paths."""
        if self._use_mbpp_id:
            return f"mbpp_id_{self.id}"
        return f"mbpp_{self.id}"

    @property
    def test_key(self) -> str:
        """Session naming key — resolves position to actual MBPP task ID."""
        if self._use_mbpp_id:
            key = f"mbpp_id_{self.id}"
        else:
            key = f"mbpp_{self._resolved_mbpp_id}"
        if self.mode != "standard":
            key += f"_{self.mode}"
        return key

    @property
    def label(self) -> str:
        tid = self._resolved_mbpp_id
        if self._use_mbpp_id:
            return f"MBPP ID{tid}"
        return f"MBPP #{tid}"

    def extract(self, cwd: str) -> tuple[str | None, str]:
        pid = self.problem_id
        input_file = f"input_{pid}.txt"
        print(f"  Extracting problem {pid}...")
        try:
            from evals.mbpp import get_problem as get_mbpp, format_text as fmt_mbpp
            data = get_mbpp(
                self.id,
                use_mbpp_id=self._use_mbpp_id,
                components=["task_description", "method_signature", "test_cases"],
            )
            text = fmt_mbpp(data)
        except Exception as e:
            return None, f"Failed to extract problem {pid}: {e}"
        Path(cwd).mkdir(parents=True, exist_ok=True)
        (Path(cwd) / input_file).write_text(text)
        return input_file, ""

    def to_dict(self) -> dict:
        d = super().to_dict()
        d["id_type"] = self.id_type
        d["id"] = self.id
        return d

    @classmethod
    def _from_dict(cls, data: dict) -> MbppProblem:
        base = DatasetProblem._base_kwargs(data)
        return cls(
            **base,
            id_type=data.get("id_type", ""),
            id=int(data.get("id", 0)),
        )


# ---------------------------------------------------------------------------
# Verina
# ---------------------------------------------------------------------------

@dataclass
class VerinaProblem(DatasetProblem):
    """VERINA benchmark problem.

    Requires both ``difficulty`` (``"basic"`` or ``"advanced"``) and ``id``.
    """

    difficulty: str = schema_field(
        "Difficulty level", required=True, default="",
        choices=["basic", "advanced"])
    id: int = schema_field(
        "Problem number within difficulty level", required=True, default=0)

    def __post_init__(self):
        super().__post_init__()
        if not self.difficulty or not self.id:
            raise ValueError("VerinaProblem requires both 'difficulty' and 'id'")

    @classmethod
    def dataset_name(cls) -> str:
        return "verina"

    @property
    def problem_id(self) -> str:
        return f"verina_{self.difficulty}_{self.id}"

    @property
    def label(self) -> str:
        return f"Verina {self.difficulty} {self.id}"

    def extract(self, cwd: str) -> tuple[str | None, str]:
        pid = self.problem_id
        input_file = f"input_{pid}.txt"
        print(f"  Extracting problem {pid}...")
        try:
            from evals.verina import get_problem as get_verina, format_text as fmt_verina
            data = get_verina(
                self.difficulty, self.id,
                components=["description", "signature", "tests", "reject_inputs"],
            )
            text = fmt_verina(data)
        except Exception as e:
            return None, f"Failed to extract problem {pid}: {e}"
        Path(cwd).mkdir(parents=True, exist_ok=True)
        (Path(cwd) / input_file).write_text(text)
        return input_file, ""

    def to_dict(self) -> dict:
        d = super().to_dict()
        d["difficulty"] = self.difficulty
        d["id"] = self.id
        return d

    @classmethod
    def _from_dict(cls, data: dict) -> VerinaProblem:
        base = DatasetProblem._base_kwargs(data)
        return cls(
            **base,
            difficulty=data.get("difficulty", ""),
            id=int(data.get("id", 0)),
        )


# ---------------------------------------------------------------------------
# Custom
# ---------------------------------------------------------------------------

@dataclass
class CustomProblem(DatasetProblem):
    """Custom problem with a user-provided identifier and spec file.

    Requires ``id`` for naming and ``input_file`` (the spec file path) for running.
    """

    id: str = schema_field(
        "Custom problem identifier", required=True, default="")

    def __post_init__(self):
        super().__post_init__()
        if not self.input_file:
            raise ValueError("CustomProblem requires 'input_file' (path to spec file)")

    @classmethod
    def dataset_name(cls) -> str:
        return "custom"

    @property
    def problem_id(self) -> str:
        return self.id or "unknown"

    @property
    def label(self) -> str:
        return f"Custom {self.id}" if self.id else "Custom ?"

    def extract(self, cwd: str) -> tuple[str | None, str]:
        return None, "No extraction supported for custom dataset"

    def to_dict(self) -> dict:
        d = super().to_dict()
        if self.id:
            d["id"] = self.id
        return d

    @classmethod
    def _from_dict(cls, data: dict) -> CustomProblem:
        base = DatasetProblem._base_kwargs(data)
        return cls(
            **base,
            id=str(data.get("id", "")),
        )

    @classmethod
    def schema(cls) -> list[SchemaField]:
        return [
            replace(f, required=True, description="Path to spec file (required for custom problems)")
            if f.name == "input_file" else f
            for f in super().schema()
        ]


# ---------------------------------------------------------------------------
# Registry + factory
# ---------------------------------------------------------------------------

_REGISTRY: dict[str, type[DatasetProblem]] = {
    "mbpp": MbppProblem,
    "verina": VerinaProblem,
    "custom": CustomProblem,
}


def parse_test_case(tc: dict) -> DatasetProblem:
    """Parse a raw JSON test-case dict into a typed ``DatasetProblem``.

    Dispatches on ``tc["dataset"]``.  Falls back to ``CustomProblem``.
    """
    ds = tc.get("dataset", "custom") or "custom"
    cls = _REGISTRY.get(ds, CustomProblem)
    return cls._from_dict(tc)


def get_schema(dataset: str) -> list[SchemaField]:
    """Get the field schema for a dataset type (for JSON generation UI)."""
    cls = _REGISTRY.get(dataset, CustomProblem)
    return cls.schema()


def available_datasets() -> list[str]:
    """Return the list of registered dataset names."""
    return list(_REGISTRY.keys())


def generate_test_file(problems: list[DatasetProblem]) -> str:
    """Serialize a list of problems to a JSON string for ``run-batch``."""
    return json.dumps([p.to_dict() for p in problems], indent=2)
