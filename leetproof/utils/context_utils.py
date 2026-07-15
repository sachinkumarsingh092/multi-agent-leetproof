"""Utilities for extracting and preparing file context for LLM prompts."""

from abc import ABC, abstractmethod

from utils.lean_proof_parser import parse_lean_decls
from utils.lean.transform import filter_map_only_defs_and_theorems
from utils.lean.parser import LeanFile


class ContextExtractor(ABC):
    """Base interface for extracting relevant context from a Lean file.

    Subclass this and implement `extract()` to create custom extractors.
    All subclasses must be picklable (no closures) for DBOS serialization.
    """

    @abstractmethod
    def extract(self, content: str) -> str:
        """Extract relevant context from file content.

        Args:
            content: Full file content as a string.

        Returns:
            Extracted context string for LLM prompts.
        """
        ...


class FullContentExtractor(ContextExtractor):
    """Returns the full file content as-is."""

    def extract(self, content: str) -> str:
        return content


class DefsAndTheoremsExtractor(ContextExtractor):
    """Extracts only definitions and theorem signatures from file content."""

    def extract(self, content: str) -> str:
        return "\n\n".join(parse_lean_decls(content, filter_map_only_defs_and_theorems))


class SectionExtractor(ContextExtractor):
    """Extracts named sections from a Lean file.

    Each section is returned with its full content and section markers.

    Examples:
        SectionExtractor(["Specs", "Impl"])
        SectionExtractor(["Specs", "Impl", "Proof"])
    """

    def __init__(self, sections: list[str]):
        self.sections = sections

    def extract(self, content: str) -> str:
        lean_file = LeanFile.from_content(content)
        parts = []
        for name in self.sections:
            section = lean_file.get_section(name)
            if section:
                parts.append(section.full_text())
        return "\n\n".join(parts)


class SpecsImplProofSignaturesExtractor(SectionExtractor):
    """Extracts Specs + Impl sections fully, and Proof section as theorem signatures only.

    Proof theorems are shown with '...' placeholders instead of full proofs,
    giving the LLM awareness of what's been proved without overwhelming context.
    """

    def __init__(self):
        super().__init__(sections=["Specs", "Impl"])

    def extract(self, content: str) -> str:
        # Specs + Impl via parent
        base = super().extract(content)

        # Proof section — signatures only
        lean_file = LeanFile.from_content(content)
        proof = lean_file.get_section("Proof")
        if proof:
            proof_decls = parse_lean_decls(proof.content, filter_map_only_defs_and_theorems)
            if proof_decls:
                proof_part = f"section Proof\n" + "\n\n".join(proof_decls) + "\nend Proof"
                return f"{base}\n\n{proof_part}" if base else proof_part

        return base
