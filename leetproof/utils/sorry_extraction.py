"""Extract sorry'd goals from a Lean file for independent proving."""

from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING

from utils.lean.parser import LeanFile
from utils.lean_proof_parser import extract_declarations, LeanTheorem

if TYPE_CHECKING:
    from utils.lean.types import Goal

logger = logging.getLogger(__name__)


@dataclass
class SorryGoal:
    """A theorem in the target section that contains sorry."""

    name: str
    theorem: LeanTheorem

    @property
    def statement(self) -> str:
        return str(self.theorem)

    @property
    def signature(self) -> str:
        parts = [self.theorem.kind.value, self.theorem.name]
        if self.theorem.params:
            parts.append(" ".join(str(p) for p in self.theorem.params))
        sig = " ".join(parts)
        if self.theorem.return_type:
            sig += " : " + self.theorem.return_type
        return sig

    @property
    def goal(self) -> Goal:
        from utils.lean.types import Goal, Param
        return Goal(
            name=self.name,
            params=[Param(name=" ".join(b.names), ty=b.type_expr) for b in self.theorem.params],
            final_goal=self.theorem.return_type or "",
        )


@dataclass
class ExtractionResult:
    """Structured output from sorry extraction."""

    imports: list[str]
    prologue_body: str
    loaded_code: str        # Prologue body + preserved sections
    target_section_code: str
    sorry_goals: list[SorryGoal]


def _has_sorry(thm: LeanTheorem) -> bool:
    if thm.proof is None:
        return False
    if thm.proof.is_by:
        return any("sorry" in t.content for t in thm.proof.tactics)
    return thm.proof.term is not None and "sorry" in thm.proof.term


def split_prologue(lean_file: LeanFile) -> tuple[list[str], str]:
    """Split a Lean file prologue into import lines and remaining body."""
    imports: list[str] = []
    body_lines: list[str] = []

    for line in lean_file.prologue.split("\n"):
        stripped = line.strip()
        if stripped.startswith("import ") and not stripped.startswith("import ("):
            imports.append(stripped.split(None, 1)[1].strip())
        else:
            body_lines.append(line)

    return imports, "\n".join(body_lines).strip()


def extract_sorry_goals(
    lean_file: LeanFile,
    target_section: str,
    preserve_sections: list[str] | None = None,
) -> ExtractionResult:
    """Extract sorry'd goals from a Lean file.

    Args:
        lean_file: Parsed LeanFile.
        target_section: Section to scan (e.g. "Proof").
        preserve_sections: Sections to include as context. Default: all except target.
    """
    # Parse prologue into imports vs body
    imports, prologue_body = split_prologue(lean_file)

    # Build context: prologue body + preserved sections
    if preserve_sections is None:
        preserve_sections = [s.name for s in lean_file.sections if s.name != target_section]

    parts = [prologue_body] if prologue_body else []
    for s in lean_file.sections:
        if s.name in preserve_sections:
            parts.append(s.full_text().strip())
    loaded_code = "\n\n".join(parts)

    # Extract sorry'd theorems from the target section
    target = lean_file.get_section(target_section)
    target_code = target.content if target else ""

    sorry_goals = [
        SorryGoal(name=d.name, theorem=d)
        for d in extract_declarations(target_code)
        if isinstance(d, LeanTheorem) and _has_sorry(d)
    ]

    logger.info(f"Extracted {len(sorry_goals)} sorry'd goals from '{target_section}'")

    return ExtractionResult(
        imports=imports,
        prologue_body=prologue_body,
        loaded_code=loaded_code,
        target_section_code=target_code,
        sorry_goals=sorry_goals,
    )
