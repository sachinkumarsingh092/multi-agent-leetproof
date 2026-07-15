"""Core data types for Lean code processing."""

from dataclasses import dataclass, asdict
from typing import Callable, List


@dataclass
class Param:
    """Represents a parameter in a Lean theorem/definition."""
    name: str
    ty: str

    def to_dict(self) -> dict:
        """Convert to JSON-serializable dict for DBOS persistence."""
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict) -> "Param":
        """Reconstruct from dict (after DBOS deserialization)."""
        return cls(**data)

    def __repr__(self):
        return f"({self.name} : {self.ty})"


@dataclass
class Goal:
    """Represents a proof goal from Lean.

    For DBOS serialization, use to_dict() before storing in state,
    and from_dict() to reconstruct when reading from state.
    """
    name: str
    params: list[Param]
    final_goal: str
    case_tag: str | None = None  # e.g., "left", "«ensures_1: postcondition a b result»"

    def to_dict(self) -> dict:
        """Convert to JSON-serializable dict for DBOS persistence.

        Uses dataclasses.asdict() which recursively converts nested dataclasses.
        """
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict) -> "Goal":
        """Reconstruct Goal from dict (after DBOS deserialization)."""
        # Reconstruct nested Param objects
        params = [Param.from_dict(p) for p in data.get("params", [])]
        return cls(
            name=data["name"],
            params=params,
            final_goal=data["final_goal"],
            case_tag=data.get("case_tag"),
        )

    def as_theorem(self) -> str:
        """Get theorem statement without proof."""
        params = '\n    '.join(str(param) for param in self.params)
        if params:
            return f"theorem {self.name}\n    {params}\n    : {self.final_goal}"
        return f"theorem {self.name} : {self.final_goal}"

    def as_sorried(self) -> str:
        """Get theorem with sorry proof."""
        return f"{self.as_theorem()} := by\n    sorry"

    def params_string(self) -> str:
        """Get params as string like '(x : Nat) (y : Int)'."""
        return " ".join(str(p) for p in self.params)

    def param_names(self) -> str:
        """Get just param names as string like 'x y'."""
        return " ".join(p.name for p in self.params)


@dataclass
class LeanDiagnostic:
    """Structured representation of a Lean diagnostic message."""
    severity: str  # "warning", "error", or "info"
    message: str
    line: int  # 1-based
    column: int  # 1-based
    line_content: str = ""
    ctx_before: str = ""
    ctx_after: str = ""

    def to_dict(self):
        return {
            "severity": self.severity,
            "message": self.message,
            "line": self.line,
            "column": self.column,
            "line_content": self.line_content,
            "ctx_before": self.ctx_before,
            "ctx_after": self.ctx_after
        }

    def __repr__(self):
        return f"[{self.severity.upper()}] Line {self.line}:{self.column}: {self.message[:80]}"

    def pp(self, include_line_no_in_ctx = True) -> str:
        """Pretty print diagnostic in a clear, LLM-friendly format."""
        lines = []
        if not (self.line <= 0):
            col = "N/A" if self.column <= 0 else self.column
            lines.append(f"[{self.severity.upper()}] Line {self.line}, Column {col}")
        lines.append(f"Message: {self.message}")

        if not (self.line <= 0):
            lines.append(f"Line: {self.line_content}")

        if self.ctx_before or self.ctx_after:
            lines.append("Context:")
            if self.ctx_before:
                ctx_lines = self.ctx_before.split('\n')
                start_line = self.line - len(ctx_lines)
                for i, ctx_line in enumerate(ctx_lines):
                    line_num = start_line + i
                    line_num_str = f"{line_num}:" if include_line_no_in_ctx else ""
                    lines.append(f"  {line_num_str} {ctx_line}")
            lines.append(f"  {self.line}: {self.line_content}  <-- {self.severity.upper()}")
            if self.ctx_after:
                ctx_lines = self.ctx_after.split('\n')
                start_line = self.line + 1
                for i, ctx_line in enumerate(ctx_lines):
                    line_num = start_line + i
                    line_num_str = f"{line_num}:" if include_line_no_in_ctx else ""
                    lines.append(f"  {line_num_str} {ctx_line}")

        return "\n".join(lines)


@dataclass
class LakeBuildResult:
    """Result of building a Lean file with lake."""
    typechecks: bool
    diagnostics: List[LeanDiagnostic]
    build_log: str = ""

    def get_messages(self, severities: List[str] | None = None) -> List[str]:
        """Get formatted diagnostic messages, optionally filtered by severity."""
        if severities:
            return [d.pp() for d in self.diagnostics if d.severity in severities]
        return [d.pp() for d in self.diagnostics]

    def error_messages(self) -> List[str]:
        """Get formatted error diagnostic messages only."""
        return self.get_messages(["error"])

    def warning_messages(self) -> List[str]:
        """Get formatted warning diagnostic messages only."""
        return self.get_messages(["warning"])

    def as_string(self, severities: List[str] | None = None, separator: str = "\n\n") -> str:
        """Get diagnostics as a single string, optionally filtered by severity."""
        return separator.join(self.get_messages(severities))

    def has_errors(self) -> bool:
        """Check if there are any error diagnostics."""
        return any(d.severity == 'error' for d in self.diagnostics)

    def assert_typechecks(self, msg: str = "Expected typecheck to pass") -> None:
        """Assert that the build succeeded, logging diagnostics on failure."""
        if not self.typechecks:
            details = self.as_string() or self.build_log or "(no diagnostics)"
            raise AssertionError(f"{msg}\n\nDiagnostics:\n{details}")

    def get_diagnostics(self, pred: Callable[ [LeanDiagnostic], bool ] | None = None) -> List[LeanDiagnostic]:
        if pred:
            return [d for d in self.diagnostics if pred(d)]
        return self.diagnostics
