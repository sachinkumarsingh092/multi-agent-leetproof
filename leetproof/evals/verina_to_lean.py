#!/usr/bin/env python3
"""
Convert a Verina benchmark problem to a spec lean file compatible with spec_bug_finder.

Usage:
    python -m utils.verina_to_lean --id verina_advanced_1 --output-file out.lean
    python -m utils.verina_to_lean --id verina_basic_1   --output-file out.lean
"""

import argparse
import json
import os
import re
import subprocess
import sys
import textwrap
import uuid
from pathlib import Path
from typing import Any


# ─── Verina loader (thin wrapper around evals.verina) ─────────────────────────

def _extract_dedented(lean_content: str, section_name: str) -> str:
    """Like extract_lean_section but uses textwrap.dedent to preserve relative indentation.

    extract_lean_section uses str.strip() on the joined text, which strips leading whitespace
    only from the first line, breaking relative indentation within the block.
    """
    start_pattern = rf'!benchmark\s+@start\s+{re.escape(section_name)}(?:\s|$)'
    end_pattern = rf'!benchmark\s+@end\s+{re.escape(section_name)}(?:\s|$)'
    lines = lean_content.split('\n')
    in_section = False
    result_lines: list[str] = []
    for line in lines:
        if re.search(start_pattern, line):
            in_section = True
            continue
        if re.search(end_pattern, line):
            break
        if in_section:
            result_lines.append(line)
    return textwrap.dedent('\n'.join(result_lines)).strip()


def load_verina_problem(problem_id: str) -> dict:
    """Load a verina problem by its full id (e.g. 'verina_advanced_1')."""
    from evals.verina import ensure_verina_repo, load_problem, extract_lean_section

    verina_dir = ensure_verina_repo()
    problem_dir = verina_dir / "datasets" / "verina" / problem_id
    if not problem_dir.exists():
        raise FileNotFoundError(f"Problem {problem_id!r} not found at {problem_dir}")

    # load_problem gives us precond/postcond body text + aux sections
    data = load_problem(problem_dir)

    # Re-extract code with textwrap.dedent to fix relative indentation
    # (extract_lean_section uses str.strip() which only strips the first line's leading spaces)
    lean_content = (problem_dir / "task.lean").read_text()
    for key in ("code", "precond", "postcond", "precond_aux", "postcond_aux", "code_aux"):
        fixed = _extract_dedented(lean_content, key)
        if fixed:
            data[key] = fixed

    data["solution_aux"] = extract_lean_section(lean_content, "solution_aux")

    # Also read signature and tests directly
    task_json = json.loads((problem_dir / "task.json").read_text())
    test_json = json.loads((problem_dir / "test.json").read_text())

    data["signature"] = task_json["signature"]
    data["tests"] = test_json
    return data


# ─── Value conversion ─────────────────────────────────────────────────────────

def _parse_python_list_str(s: str) -> list[str]:
    """Parse a Python-list string like '[1, -2, 3]' into a list of element strings."""
    s = s.strip()
    if s.startswith("[") and s.endswith("]"):
        inner = s[1:-1].strip()
        if not inner:
            return []
        # simple split — handles integers; won't handle nested lists (extend if needed)
        return [e.strip() for e in inner.split(",")]
    return [s]


def _is_lean_literal(s: str) -> bool:
    """Return True if the string already looks like a Lean literal (list, array, tuple, etc.)."""
    s = s.strip()
    return (
        s.startswith("#[")   # Array
        or (s.startswith("[") and s.endswith("]"))   # List
        or (s.startswith("(") and s.endswith(")"))   # Tuple / product
        or s in ("true", "false")
    )


def python_to_lean(value: Any, lean_type: str) -> str:
    """Convert a JSON test value to a Lean literal given the Lean type."""
    lean_type = lean_type.strip()

    # If the value is already a Lean literal string, return it verbatim
    if isinstance(value, str) and _is_lean_literal(value):
        return value.strip()

    if lean_type.startswith("List "):
        if isinstance(value, list):
            elems = [python_to_lean(e, lean_type[5:]) for e in value]
        else:
            elems = _parse_python_list_str(str(value))
        return "[" + ", ".join(elems) + "]"

    if lean_type.startswith("Array "):
        if isinstance(value, list):
            elems = [python_to_lean(e, lean_type[6:]) for e in value]
        else:
            elems = _parse_python_list_str(str(value))
        return "#[" + ", ".join(elems) + "]"

    if lean_type == "Bool":
        if isinstance(value, bool):
            return "true" if value else "false"
        return str(value).lower()

    if lean_type in ("Int", "Nat", "Float"):
        return str(value)

    if lean_type == "String":
        return f'"{value}"'

    if lean_type == "Char":
        return f"'{value}'"

    # fallback
    return str(value)


# ─── Lean file generator ──────────────────────────────────────────────────────

STANDARD_HEADER = """\
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic\
"""

SET_OPTIONS = """\
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"\
"""


def _remove_h_precond(text: str) -> str:
    """Remove any '(h_precond : ...)' binder from a def signature line."""
    return re.sub(r'\s*\(h_precond\s*:[^)]*\)', '', text)


def build_lean_file(data: dict, include_decidable: bool = True) -> str:
    sig = data["signature"]
    params = sig["parameters"]          # list of {param_name, param_type}
    return_type = sig["return_type"]
    fn_name = sig["name"]

    # ── Imports ────────────────────────────────────────────────────────────────
    task_imports = (data.get("task_imports") or "").strip()
    header_lines = [STANDARD_HEADER]
    if task_imports:
        # Filter out imports already in our standard header
        skip = {
            "import Mathlib",
            "import Mathlib.Tactic",
        }
        for line in task_imports.splitlines():
            if line.strip() and line.strip() not in skip:
                header_lines.append(line.strip())
    header = "\n".join(header_lines)

    # ── Helpers / aux sections ────────────────────────────────────────────────
    aux_parts = []
    for key in ("precond_aux", "postcond_aux", "solution_aux"):
        block = (data.get(key) or "").strip()
        if block:
            aux_parts.append(block)
    helpers = "\n\n".join(aux_parts)

    # ── Precondition ───────────────────────────────────────────────────────────
    precond_body = (data.get("precond") or "True").strip()
    param_sig = " ".join(f"({p['param_name']} : {p['param_type']})" for p in params)
    param_call = " ".join(p["param_name"] for p in params)
    precond_def = f"def precondition {param_sig} : Prop :=\n  {precond_body}"

    decidable_inst = (
        f"instance instDecidablePrecond {param_sig} : Decidable (precondition {param_call}) := by\n"
        f"  unfold precondition\n"
        f"  infer_instance"
    )

    # ── Postcondition ──────────────────────────────────────────────────────────
    postcond_body = (data.get("postcond") or "True").strip()
    postcond_def = (
        f"def postcondition {param_sig} (result : {return_type}) :=\n"
        f"  {postcond_body}"
    )

    # ── Implementation ────────────────────────────────────────────────────────
    code_body = (data.get("code") or "").strip()
    code_aux = (data.get("code_aux") or "").strip()
    impl_lines = []
    if code_body:
        if code_aux:
            impl_lines += [code_aux, ""]
        impl_lines.append(f"def {fn_name} {param_sig} : {return_type} :=")
        for line in code_body.splitlines():
            impl_lines.append(f"  {line}" if line.strip() else line)
        impl_lines.append("")

    # ── Test cases ────────────────────────────────────────────────────────────
    tests = data.get("tests") or []
    test_lines = []

    for i, test in enumerate(tests, 1):
        inp = test.get("input", {})
        expected = test.get("expected")

        for p in params:
            pname = p["param_name"]
            ptype = p["param_type"]
            val_str = python_to_lean(inp[pname], ptype)
            test_lines.append(f"def test{i}_{pname} : {ptype} := {val_str}")

        exp_str = python_to_lean(expected, return_type)
        test_lines.append(f"def test{i}_Expected : {return_type} := {exp_str}")
        test_lines.append("")

    # ── Assemble ───────────────────────────────────────────────────────────────
    parts = [
        header,
        "",
        SET_OPTIONS,
        "",
        f"-- Problem: {fn_name}",
        "",
        "section Specs",
        "",
        "register_specdef_allow_recursion",
        "",
    ]

    if helpers:
        parts += [helpers, ""]

    spec_middle = [precond_def, ""]
    if include_decidable:
        spec_middle += [decidable_inst, ""]
    spec_middle += [postcond_def]

    parts += spec_middle + [
        "",
        "end Specs",
        "",
    ]

    if impl_lines:
        parts += ["section Impl", ""] + impl_lines + ["end Impl", ""]

    parts += [
        "section TestCases",
        "",
    ]
    parts += test_lines
    parts += [
        "end TestCases",
    ]

    return "\n".join(parts)


# ─── Build check ──────────────────────────────────────────────────────────────

def _output_file_to_module(output_file: str, build_dir: str) -> str:
    rel = os.path.relpath(os.path.abspath(output_file), os.path.abspath(build_dir))
    if rel.endswith(".lean"):
        rel = rel[:-5]
    return rel.replace(os.sep, ".")


def _decidable_failed(stdout: str, stderr: str) -> bool:
    """Return True if the build error is specifically from the Decidable instance."""
    combined = stdout + "\n" + stderr
    return (
        "instDecidablePrecond" in combined
        or ("failed to synthesize" in combined and "Decidable" in combined)
        or ("infer_instance" in combined and "error" in combined)
    )


def build_and_check_decidable(data: dict, out: Path, build_dir: str) -> bool:
    """Write file with Decidable instance, build it, fall back without if it fails.
    Returns True if the instance was kept, False if it was dropped.
    """
    module = _output_file_to_module(str(out), build_dir)

    # First try: with instance
    out.write_text(build_lean_file(data, include_decidable=True), encoding="utf-8")
    result = subprocess.run(
        ["lake", "build", module],
        cwd=build_dir, capture_output=True, text=True,
    )

    if result.returncode == 0 or not _decidable_failed(result.stdout, result.stderr):
        # Build passed, or failed for unrelated reasons — keep the instance
        return True

    # Instance caused the failure — regenerate without it
    out.write_text(build_lean_file(data, include_decidable=False), encoding="utf-8")
    return False


# ─── Sampler: generate test cases via Plausible Gen ──────────────────────────

def _build_sampler_section(data: dict, temp_file: str, n: int = 15) -> str:
    """Build a `run_elab do` section that samples valid inputs and writes them to temp_file."""
    sig = data["signature"]
    params = sig["parameters"]
    fn_name = sig["name"]
    param_call = " ".join(p["param_name"] for p in params)

    sample_lines = []
    for p in params:
        pname = p["param_name"]
        ptype = p["param_type"]
        sample_lines.append(
            f"    let {pname} ← Plausible.Gen.run "
            f"(Plausible.SampleableExt.interpSample ({ptype})) 20"
        )

    param_repr_lines = []
    for p in params:
        pname = p["param_name"]
        # Build Lean string interpolation without Python f-string substitution on {repr ...}
        param_repr_lines.append(
            "      lines := lines.push s!\"LOOM_PARAM_" + pname + "={repr " + pname + "}\""
        )

    all_lines = [
        "section Sampler",
        "run_elab do",
        "  let mut lines : Array String := #[]",
        "  let mut count : Nat := 0",
        "  for _ in List.range 2000 do",
        f"    if count >= {n} then break",
    ]
    all_lines += sample_lines
    all_lines += [
        f"    if decide (precondition {param_call}) then",
        f"      let result := {fn_name} {param_call}",
        '      lines := lines.push "LOOM_START"',
    ]
    all_lines += param_repr_lines
    all_lines += [
        '      lines := lines.push s!"LOOM_RESULT={repr result}"',
        '      lines := lines.push "LOOM_END"',
        "      count := count + 1",
        f'  IO.FS.writeFile "{temp_file}" (String.intercalate "\\n" lines.toList)',
        "end Sampler",
    ]
    return "\n".join(all_lines)


def _is_loom_keyword(line: str) -> bool:
    s = line.strip()
    return s in ("LOOM_START", "LOOM_END") or s.startswith("LOOM_PARAM_") or s.startswith("LOOM_RESULT=")


def _parse_sampler_file(content: str, data: dict) -> list[dict]:
    """Parse the sampler output file into dicts {param_name: lean_literal, '__result__': val}.

    Handles multi-line repr values: lines that don't start with a LOOM keyword
    are treated as continuations of the previous value.
    """
    params = data["signature"]["parameters"]
    results = []

    lines = content.splitlines()
    i = 0
    while i < len(lines):
        if lines[i].strip() == "LOOM_START":
            entry: dict = {}
            i += 1
            current_key: str | None = None
            while i < len(lines) and lines[i].strip() != "LOOM_END":
                line = lines[i]
                stripped = line.strip()
                if stripped.startswith("LOOM_PARAM_"):
                    rest = stripped[len("LOOM_PARAM_"):]
                    eq = rest.index("=")
                    pname, pval = rest[:eq], rest[eq + 1:]
                    entry[pname] = pval
                    current_key = pname
                elif stripped.startswith("LOOM_RESULT="):
                    entry["__result__"] = stripped[len("LOOM_RESULT="):]
                    current_key = "__result__"
                elif current_key is not None and not _is_loom_keyword(line):
                    entry[current_key] += stripped
                i += 1
            if all(p["param_name"] in entry for p in params) and "__result__" in entry:
                results.append(entry)
            i += 1  # skip LOOM_END
        else:
            i += 1
    return results


def generate_sampled_tests(data: dict, out: Path, build_dir: str, n: int = 15) -> list[dict]:
    """Append a Lean sampler section to `out`, build it, parse the written temp file.

    Returns a list of sample dicts (param -> lean literal, plus '__result__').
    Always restores `out` to its original content.
    """
    if not data.get("code"):
        return []  # No implementation to run

    temp_file = f"/tmp/loom_sampler_{uuid.uuid4().hex}.txt"
    sampler_code = _build_sampler_section(data, temp_file, n)

    original = out.read_text(encoding="utf-8")
    out.write_text(original + "\n\n" + sampler_code + "\n", encoding="utf-8")

    samples: list[dict] = []
    try:
        module = _output_file_to_module(str(out), build_dir)
        subprocess.run(
            ["lake", "build", module],
            cwd=build_dir, capture_output=True, text=True,
        )
        tmp = Path(temp_file)
        if tmp.exists():
            samples = _parse_sampler_file(tmp.read_text(encoding="utf-8"), data)
            tmp.unlink(missing_ok=True)
    finally:
        out.write_text(original, encoding="utf-8")

    return samples


def _append_sampled_test_cases(lean_content: str, samples: list[dict],
                                data: dict, existing_count: int) -> str:
    """Insert sampled test case defs before `end TestCases`."""
    if not samples:
        return lean_content

    params = data["signature"]["parameters"]
    return_type = data["signature"]["return_type"]

    end_marker = "end TestCases"
    idx = lean_content.rfind(end_marker)
    if idx == -1:
        return lean_content

    new_lines: list[str] = []
    for i, sample in enumerate(samples, existing_count + 1):
        for p in params:
            pname = p["param_name"]
            ptype = p["param_type"]
            new_lines.append(f"def test{i}_{pname} : {ptype} := {sample[pname]}")
        new_lines.append(f"def test{i}_Expected : {return_type} := {sample['__result__']}")
        new_lines.append("")

    insert_text = "\n".join(new_lines)
    return lean_content[:idx] + insert_text + lean_content[idx:]


# ─── CLI ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Convert a Verina problem to a spec lean file for PBT"
    )
    parser.add_argument("--id", required=True,
                        help="Verina problem id, e.g. 'verina_advanced_1'")
    parser.add_argument("--output-file", required=True,
                        help="Output .lean file path")
    parser.add_argument("--build-dir",
                        help="If given, run lake build to verify the Decidable instance")
    parser.add_argument("--sample", type=int, default=0,
                        help="If > 0 and --build-dir is set, sample this many extra test cases "
                             "via Plausible Gen (requires Decidable instance to succeed)")
    args = parser.parse_args()

    try:
        data = load_verina_problem(args.id)
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    out = Path(args.output_file)
    out.parent.mkdir(parents=True, exist_ok=True)

    if args.build_dir:
        kept = build_and_check_decidable(data, out, args.build_dir)
        status = "with Decidable instance" if kept else "WITHOUT Decidable instance (synthesis failed)"
        print(f"Written: {out}  [{status}]")

        if kept and args.sample > 0:
            print(f"  Sampling {args.sample} extra test cases via Plausible Gen...")
            samples = generate_sampled_tests(data, out, args.build_dir, n=args.sample)
            if samples:
                existing = len(data.get("tests") or [])
                content = out.read_text(encoding="utf-8")
                content = _append_sampled_test_cases(content, samples, data, existing)
                out.write_text(content, encoding="utf-8")
                print(f"  Added {len(samples)} sampled test cases")
            else:
                print("  No sampled test cases generated (sampler produced no output)")
    else:
        out.write_text(build_lean_file(data), encoding="utf-8")
        print(f"Written: {out}")


if __name__ == "__main__":
    main()
