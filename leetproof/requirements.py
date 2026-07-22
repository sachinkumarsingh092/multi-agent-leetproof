"""Shared format contract for reviewed natural-language specifications."""

import re


REQUIRED_SECTIONS = (
    "=== TASK_DESCRIPTION ===",
    "=== METHOD_SIGNATURE ===",
    "=== TEST_CASES ===",
)


def validate_requirements(text: str) -> None:
    """Require one method in the reviewed three-section pipeline format."""
    missing = [section for section in REQUIRED_SECTIONS if section not in text]
    if missing:
        raise ValueError(
            "Reviewed specification is missing required sections: "
            + ", ".join(missing)
        )

    signature_section = text.split(REQUIRED_SECTIONS[1], 1)[1].split(
        REQUIRED_SECTIONS[2], 1
    )[0]
    method_count = len(
        re.findall(r"(?m)^\s*method\s+[A-Za-z_][A-Za-z0-9_]*\s*\(", signature_section)
    )
    if method_count != 1:
        raise ValueError(
            "Reviewed specification must contain exactly one method signature; "
            f"found {method_count}. Split multi-method work into separate "
            "prepare and pipeline runs."
        )
