#!/usr/bin/env python3
"""
Interactive batch payload generator.

Builds a problems.json file for run-batch by walking through
the DatasetProblem schemas and prompting the user for values.

The interactive flow is fully driven by schema metadata (groups,
required_when, choices, FieldType) — no hardcoded field knowledge.

Usage:
    lloom-agent gen-batch
    lloom-agent gen-batch -o my_tests.json
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from evals.dataset import (
    FieldType,
    SchemaField,
    available_datasets,
    generate_test_file,
    get_schema,
    parse_test_case,
)


# ---------------------------------------------------------------------------
# Prompt helpers
# ---------------------------------------------------------------------------

def _ask(prompt: str, default: str | None = None) -> str:
    """Prompt for a string value with optional default."""
    suffix = f" [{default}]" if default else ""
    try:
        raw = input(f"  {prompt}{suffix}: ").strip()
    except (EOFError, KeyboardInterrupt):
        print()
        sys.exit(0)
    return raw or (default or "")


def _ask_bool(prompt: str, default: bool = False) -> bool:
    """Prompt for a yes/no value."""
    hint = "Y/n" if default else "y/N"
    try:
        raw = input(f"  {prompt} ({hint}): ").strip().lower()
    except (EOFError, KeyboardInterrupt):
        print()
        sys.exit(0)
    if not raw:
        return default
    return raw in ("y", "yes", "1", "true")


def _ask_choice(prompt: str, choices: list[str]) -> str:
    """Prompt with numbered choices."""
    print(f"  {prompt}")
    for i, c in enumerate(choices, 1):
        print(f"    {i}) {c}")
    while True:
        try:
            raw = input("  > ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            sys.exit(0)
        if raw.isdigit() and 1 <= int(raw) <= len(choices):
            return choices[int(raw) - 1]
        if raw in choices:
            return raw
        print(f"  Please enter 1-{len(choices)} or one of: {', '.join(choices)}")


# ---------------------------------------------------------------------------
# Schema-driven field prompting
# ---------------------------------------------------------------------------

def _prompt_field(f: SchemaField) -> object | None:
    """Prompt the user for one schema field. Returns None to skip."""
    label = f"{f.description} ({f.name})"

    if f.type == FieldType.BOOL:
        return _ask_bool(label, default=bool(f.default))

    if f.choices:
        return _ask_choice(f"{label}:", f.choices)

    if f.type == FieldType.INT:
        default_hint = str(f.default) if f.default else None
        raw = _ask(label, default=default_hint)
        if not raw:
            return None
        return int(raw)

    # FieldType.STR
    default_hint = str(f.default) if f.default else None
    raw = _ask(label, default=default_hint)
    return raw or None


def _is_field_required(f: SchemaField, tc: dict) -> bool:
    """Check if a field is required given current collected values.

    A field is required if:
    - ``f.required`` is True, OR
    - ``f.required_when`` matches the current test case values.
    """
    if f.required:
        return True
    if f.required_when:
        for key, values in f.required_when.items():
            if tc.get(key) in values:
                return True
    return False


# ---------------------------------------------------------------------------
# Build one test case interactively
# ---------------------------------------------------------------------------

def _build_entry() -> dict | None:
    """Walk the user through creating one test case entry.

    The flow is fully driven by the schema:
    1. Pick dataset
    2. Prompt identity fields (no group — always required)
    3. Prompt config fields grouped by schema group
    4. Validate via parse_test_case
    5. Preview

    Returns the validated dict, or None if the user cancels.
    """
    datasets = available_datasets()
    ds = _ask_choice("Dataset:", datasets)
    schema = get_schema(ds)

    # Split into identity (no group) and config (has group)
    identity = [f for f in schema if not f.group]
    config = [f for f in schema if f.group]

    tc: dict = {"dataset": ds}

    # 1. Prompt identity fields (always required)
    if identity:
        print()
        for f in identity:
            while True:
                val = _prompt_field(f)
                if val is not None and val != "":
                    tc[f.name] = val
                    break
                print(f"    '{f.name}' is required.")

    # 2. Prompt config fields grouped by schema group
    groups: dict[str, list[SchemaField]] = {}
    for f in config:
        assert f.group is not None
        groups.setdefault(f.group, []).append(f)

    for group_name, fields in groups.items():
        has_required = any(_is_field_required(f, tc) for f in fields)

        print()
        # Optional groups — ask before showing fields
        if not has_required:
            if not _ask_bool(f"Configure {group_name.lower()}?", default=False):
                continue

        for f in fields:
            required = _is_field_required(f, tc)
            if required:
                while True:
                    val = _prompt_field(f)
                    if val is not None and val != "":
                        tc[f.name] = val
                        break
                    print(f"    '{f.name}' is required.")
            else:
                val = _prompt_field(f)
                if val is not None and val != "" and val != f.default:
                    tc[f.name] = val

    # 3. Validate
    print()
    try:
        problem = parse_test_case(tc)
    except (ValueError, KeyError) as e:
        print(f"  Validation error: {e}")
        if _ask_bool("Try again?", default=True):
            return _build_entry()
        return None

    # 4. Preview
    clean = problem.to_dict()
    print(f"  -> {problem.label}")
    print(f"     {json.dumps(clean)}")
    return clean


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Interactively generate a problems.json for run-batch.",
    )
    parser.add_argument(
        "-o", "--output", default="problems.json",
        help="Output JSON file path (default: problems.json)",
    )
    parser.add_argument(
        "-a", "--append", action="store_true",
        help="Append to existing file instead of overwriting",
    )
    args = parser.parse_args()

    print("Batch payload generator")
    print("=" * 40)
    print(f"Output: {args.output}")
    print()

    entries: list[dict] = []

    # Load existing entries if appending
    if args.append and Path(args.output).exists():
        try:
            existing = json.loads(Path(args.output).read_text())
            if isinstance(existing, list):
                entries.extend(existing)
                print(f"Loaded {len(entries)} existing entries.")
                print()
        except Exception as e:
            print(f"Warning: could not load {args.output}: {e}")
            print()

    while True:
        print(f"--- Entry #{len(entries) + 1} ---")
        entry = _build_entry()
        if entry:
            entries.append(entry)
            print()

        if not _ask_bool("Add another entry?", default=True):
            break
        print()

    if not entries:
        print("No entries created.")
        return

    # Write output
    output = generate_test_file(
        [parse_test_case(e) for e in entries]
    )
    Path(args.output).write_text(output + "\n")
    print(f"\nWrote {len(entries)} entries to {args.output}")


if __name__ == "__main__":
    main()
