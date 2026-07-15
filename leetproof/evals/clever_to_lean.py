#!/usr/bin/env python3
"""
Convert a CLEVER benchmark problem to a spec lean file compatible with spec_bug_finder.

Usage:
    python -m utils.clever_to_lean --id 0 --output-file out.lean
    python -m utils.clever_to_lean --id 42 --output-file out.lean
"""

import argparse
import ast
import os
import re
import subprocess
import sys
import uuid
from pathlib import Path
from typing import Any


# ─── CLEVER loader ────────────────────────────────────────────────────────────

def load_clever_problem(problem_id: int):
    """Load a CLEVER problem by its index (0-based)."""
    from clever_bench.benchmark import Benchmark

    benchmark = Benchmark()
    benchmark.load_all()
    return benchmark.get_problem(problem_id)


# ─── Signature parser ─────────────────────────────────────────────────────────

def _extract_top_level_paren_groups(text: str) -> list[str]:
    """Return the contents (without outer parens) of each top-level (...) group."""
    groups: list[str] = []
    depth = 0
    start: int | None = None
    for i, ch in enumerate(text):
        if ch == "(" and depth == 0:
            start = i
            depth = 1
        elif ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(text[start + 1 : i])
                start = None
    return groups


def parse_impl_signature(impl_sig: str) -> tuple[list[dict], str]:
    """
    Parse 'def implementation (p1 : T1) (p2 : T2) : RetType :='
    into a list of {param_name, param_type} dicts and the return type string.

    Also handles the grouped form '(p1 p2 : T)' used by some CLEVER problems.
    Uses a depth-aware parser to handle nested parentheses in types.
    """
    params = []
    for group in _extract_top_level_paren_groups(impl_sig):
        group = group.strip()
        if ':' not in group:
            continue
        colon_idx = group.index(':')
        names_part = group[:colon_idx].strip()
        type_part  = group[colon_idx + 1:].strip()
        # names_part can be one or more identifiers separated by spaces
        for name in names_part.split():
            if re.match(r'^\w+$', name):
                params.append({"param_name": name, "param_type": type_part})

    ret_match = re.search(r'\)\s*:\s*(.+?)\s*:=', impl_sig)
    if not ret_match:
        # No parenthesised params — return type follows function name directly
        ret_match = re.search(r'implementation\s*:\s*(.+?)\s*:=', impl_sig)
    return_type = ret_match.group(1).strip() if ret_match else "?"

    return params, return_type


# ─── Value conversion ─────────────────────────────────────────────────────────

def _is_lean_literal(s: str) -> bool:
    s = s.strip()
    return (
        s.startswith("#[")
        or (s.startswith("[") and s.endswith("]"))
        or (s.startswith("(") and s.endswith(")"))
        or s in ("true", "false")
    )


def python_to_lean(value: Any, lean_type: str) -> str:
    """Convert a Python/YAML test value to a Lean literal given the Lean type."""
    lean_type = lean_type.strip()

    if lean_type.startswith("Option "):
        inner_type = lean_type[7:]
        if value is None or value == "None":
            return "none"
        inner = python_to_lean(value, inner_type)
        # Wrap in parens if the inner value needs it (negative numbers, spaces)
        if " " in inner or inner.startswith("-"):
            inner = f"({inner})"
        return f"some {inner}"

    if value is None:
        return "sorry"

    # Handle string/char types first — a Python string is the value, not a Lean literal
    if lean_type == "String":
        if isinstance(value, str):
            escaped = value.replace("\\", "\\\\").replace('"', '\\"')
            return f'"{escaped}"'
        return f'"{value}"'

    if lean_type == "Char":
        return f"'{value}'"

    # If the value is already a Lean literal string, return it verbatim
    if isinstance(value, str) and _is_lean_literal(value):
        return value.strip()

    if lean_type.startswith("List "):
        elem_type = lean_type[5:]
        if isinstance(value, list):
            elems = [python_to_lean(e, elem_type) for e in value]
        else:
            elems = [str(value)]
        return "[" + ", ".join(elems) + "]"

    if lean_type.startswith("Array "):
        elem_type = lean_type[6:]
        if isinstance(value, list):
            elems = [python_to_lean(e, elem_type) for e in value]
        else:
            elems = [str(value)]
        return "#[" + ", ".join(elems) + "]"

    if lean_type == "Bool":
        if isinstance(value, bool):
            return "true" if value else "false"
        return str(value).lower()

    if lean_type in ("Int", "Nat"):
        return str(int(value))

    if lean_type in ("Float", "Rat"):
        return str(value)

    # Product type: "A × B" or "A × B × C"
    if " × " in lean_type:
        parts = [t.strip() for t in lean_type.split(" × ")]
        if isinstance(value, (list, tuple)) and len(value) == len(parts):
            elems = [python_to_lean(v, t) for v, t in zip(value, parts)]
            return "(" + ", ".join(elems) + ")"

    # fallback
    return str(value)


# ─── Spec let extractor ───────────────────────────────────────────────────────

def parse_spec_non_impl_params(ground_truth_spec: str) -> tuple[list[dict], int]:
    """
    Parse a problem_spec definition header to find non-impl params and the
    position of the top-level ':='.

    Returns (params, assign_pos).  assign_pos == -1 if ':=' not found.
    """
    depth = 0
    assign_pos = -1
    i = 0
    while i < len(ground_truth_spec) - 1:
        ch = ground_truth_spec[i]
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ground_truth_spec[i : i + 2] == ":=" and depth == 0:
            assign_pos = i
            break
        i += 1

    if assign_pos == -1:
        return [], -1

    header = ground_truth_spec[:assign_pos]
    params: list[dict] = []
    for group in _extract_top_level_paren_groups(header):
        group = group.strip()
        if ":" not in group:
            continue
        colon_idx = group.index(":")
        names_part = group[:colon_idx].strip()
        type_part = group[colon_idx + 1 :].strip()
        # Skip the impl/implementation parameter: it is a function (its type contains →)
        if "→" in type_part:
            continue
        for name in names_part.split():
            if re.match(r"^\w+$", name):
                params.append({"param_name": name, "param_type": type_part})

    return params, assign_pos


def find_spec_let(
    extracted_lets: list[tuple[str, str, str]], return_type: str
) -> tuple[str | None, str | None, str | None]:
    """
    Find the 'spec' let: the extracted let whose extra params contain a
    parameter whose type equals *return_type*.

    First tries typed params ``(res : RetType)``; falls back to untyped
    single-identifier params ``(res)`` if no typed match is found.

    Returns (let_name, result_var_name, let_body) or (None, None, None).
    """
    rt = return_type.strip()
    # Strip spurious outer parens, e.g. "(Int)" → "Int"
    while rt.startswith("(") and rt.endswith(")"):
        rt = rt[1:-1].strip()
    typed_candidates: list[tuple[str, str, str]] = []
    untyped_candidate: tuple[str, str, str] | None = None

    for name, extra_params, body in extracted_lets:
        if not extra_params:
            continue
        for group in _extract_top_level_paren_groups(extra_params):
            group = group.strip()
            if ":" in group:
                colon_idx = group.index(":")
                pname = group[:colon_idx].strip()
                ptype = group[colon_idx + 1 :].strip()
                _pt = ptype
                while _pt.startswith("(") and _pt.endswith(")"):
                    _pt = _pt[1:-1].strip()
                if _pt == rt:
                    typed_candidates.append((name, pname, body))
            elif re.match(r"^\w+$", group) and untyped_candidate is None:
                # Single untyped identifier — remember as fallback
                untyped_candidate = (name, group, body)

    if typed_candidates:
        # Prefer a let literally named "spec"; otherwise take the first match.
        for candidate in typed_candidates:
            if candidate[0] == "spec":
                return candidate
        return typed_candidates[0]

    if untyped_candidate:
        return untyped_candidate
    return None, None, None


def split_on_implication_arrow(text: str) -> list[str]:
    """Split *text* on the Unicode implication arrow '→' at paren-depth 0."""
    parts: list[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "→" and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return [p.strip() for p in parts]


def extract_precond_and_postcond(
    spec_let_body: str, result_var: str
) -> tuple[list[str], str]:
    """
    Split *spec_let_body* on '→' at depth 0.
    Leading segments that do **not** contain *result_var* become preconditions.
    The remaining segments (joined back with '→') become the postcondition.

    Returns (precond_parts, postcond_body).
    """
    segments = split_on_implication_arrow(spec_let_body)
    precond_parts: list[str] = []
    i = 0
    # Never consume the last segment as a precondition
    while i < len(segments) - 1:
        seg = segments[i]
        if not re.search(r"\b" + re.escape(result_var) + r"\b", seg):
            precond_parts.append(seg)
            i += 1
        else:
            break
    postcond = " →\n  ".join(segments[i:])
    return precond_parts, postcond


def _find_let_semi(text: str, start: int = 0) -> int | None:
    """
    Find the index of the ';' that terminates a Lean let-body in *text*
    starting at *start*, skipping over nested ``let … := …;`` patterns.

    A ';' is considered the terminator only when it is at paren-depth 0
    AND not consumed by a nested let-binding.
    """
    depth = 0
    i = start
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in "([{":
            depth += 1
            i += 1
        elif ch in ")]}":
            depth -= 1
            i += 1
        elif ch == ";" and depth == 0:
            return i
        elif depth == 0 and text[i : i + 4] == "let " and (i == 0 or not text[i - 1].isalnum()):
            # Nested let: consume it (find its own := and then its own ;)
            j = i + 4
            d2 = 0
            assign_j: int | None = None
            while j < n - 1:
                c = text[j]
                if c in "([{":
                    d2 += 1
                elif c in ")]}":
                    d2 -= 1
                elif text[j : j + 2] == ":=" and d2 == 0:
                    assign_j = j
                    break
                j += 1
            if assign_j is not None:
                nested_end = _find_let_semi(text, assign_j + 2)
                if nested_end is not None:
                    i = nested_end + 1
                    continue
            i += 1
        else:
            i += 1
    return None


def _first_sibling_let(text: str) -> int | None:
    """
    Scan *text* for the first ``\\nlet `` at depth 0 that is a SIBLING binding
    (i.e. has NO ';' terminator — so it cannot be consumed as a nested let).

    Lets that DO have a ';' terminator are nested inside the current let body
    and are skipped over.  Returns the position of the '\\n' in '\\nlet ', or
    None if no sibling let is found.
    """
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in "([{":
            depth += 1
            i += 1
        elif ch in ")]}":
            depth -= 1
            i += 1
        elif depth == 0 and text[i : i + 5] == "\nlet " and (i == 0 or not text[i - 1].isalnum()):
            # Found a '\nlet ' at depth 0. Determine if it has a ';' terminator.
            j = i + 5
            d2 = 0
            assign_j: int | None = None
            while j < n - 1:
                c = text[j]
                if c in "([{":
                    d2 += 1
                elif c in ")]}":
                    d2 -= 1
                elif text[j : j + 2] == ":=" and d2 == 0:
                    assign_j = j
                    break
                j += 1
            if assign_j is not None:
                semi = _find_let_semi(text, assign_j + 2)
                if semi is not None:
                    # Nested (terminated) let — skip past it and continue
                    i = semi + 1
                    continue
            # No ';' terminator → this is a sibling let
            return i
        else:
            i += 1
    return None


def extract_top_level_lets(body: str) -> tuple[list[tuple[str, str, str]], str]:
    """
    Extract top-level ``let name (extra_params) := body;`` bindings from
    a Lean term body.  Only bindings terminated by a ';' at paren-depth 0
    are considered top-level.

    Returns (lets, remaining_body) where
        lets = [(name, extra_params_str, let_body_str), ...]
    and remaining_body is everything after the last extracted let.
    """
    lets: list[tuple[str, str, str]] = []
    remaining = body.strip()

    while remaining.startswith("let "):
        # --- find ':=' at depth 0 (skip the 'let ' prefix) ---
        depth = 0
        assign_idx: int | None = None
        i = 4  # len("let ")
        while i < len(remaining) - 1:
            ch = remaining[i]
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            elif remaining[i : i + 2] == ":=" and depth == 0:
                assign_idx = i
                break
            i += 1
        if assign_idx is None:
            break

        # header is the text between 'let ' and ':='
        header = remaining[4:assign_idx].strip()
        paren_idx = header.find("(")
        if paren_idx == -1:
            # Possible type annotation: "name : Type" — strip it
            colon_idx = header.find(":")
            name = header[:colon_idx].strip() if colon_idx != -1 else header.strip()
            extra_params = ""
        elif ":" in header[:paren_idx]:
            # Type annotation with parens: "name : SomeType (Args)"
            # A ':' before the first '(' means the '(' is part of a type, not params.
            colon_idx = header.index(":")
            name = header[:colon_idx].strip()
            extra_params = ""
        else:
            name = header[:paren_idx].strip()
            extra_params = header[paren_idx:].strip()

        # --- find terminating ';' at depth 0 in the body ---
        rest = remaining[assign_idx + 2 :]
        semi_idx = _find_let_semi(rest)
        if semi_idx is None:
            # Fallback for lets without a ';' terminator.
            # A sibling let (no ';') is a valid boundary; nested (';'-terminated)
            # lets inside the body are skipped over by _first_sibling_let.
            sibling_pos = _first_sibling_let(rest)
            exist_m = re.search(r"\n∃\s", rest)
            if sibling_pos is not None and exist_m is not None:
                fb_end = min(sibling_pos, exist_m.start())
            elif sibling_pos is not None:
                fb_end = sibling_pos
            elif exist_m is not None:
                fb_end = exist_m.start()
            else:
                break  # no boundary found at all
            let_body = rest[:fb_end].strip().rstrip(";").strip()
            lets.append((name, extra_params, let_body))
            remaining = rest[fb_end:].strip()
            if remaining.startswith("∃"):
                break  # nothing more to extract
            continue  # might be another let

        let_body = rest[:semi_idx].strip()
        lets.append((name, extra_params, let_body))
        remaining = rest[semi_idx + 1 :].strip()

    return lets, remaining


# ─── Lean file generator ──────────────────────────────────────────────────────

STANDARD_HEADER = """\
import Extensions.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic"""

SET_OPTIONS = """\
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic\""""


def build_lean_file(problem, include_decidable: bool = True) -> str:
    impl_sig = (problem.implementation_signature or "").strip()
    params, return_type = parse_impl_signature(impl_sig)
    fn_name = f"problem_{problem.problem_id}"

    # ── Helper definitions ─────────────────────────────────────────────────────
    # All helper definitions are already provided by `import Extensions.CleverAllImports`,
    # so we skip them here to avoid duplicate-definition errors.

    # ── Ground truth spec (include verbatim — defines problem_spec) ───────────
    ground_truth_spec = (problem.problem_spec_formal_ground_truth or "").strip()

    # ── Extract top-level lets from problem_spec for standalone defs ──────────
    # Strip `-- ...` line comments before parsing so they don't confuse the
    # let-extractor; the original ground_truth_spec is still used for output.
    _spec_for_parsing = re.sub(r"--[^\n]*", "", ground_truth_spec)
    spec_var_params: list[dict] = []
    extracted_lets: list[tuple[str, str, str]] = []
    _remaining_spec_body: str = ""
    if ground_truth_spec:
        spec_var_params, assign_pos = parse_spec_non_impl_params(_spec_for_parsing)
        if assign_pos != -1:
            spec_body = _spec_for_parsing[assign_pos + 2 :].strip()
            extracted_lets, _remaining_spec_body = extract_top_level_lets(spec_body)

    # ── Precondition / Postcondition ──────────────────────────────────────────
    # Use spec param names (from problem_spec) when available so the postcondition
    # body (which references spec param names) stays consistent with the signature.
    _sig_params = spec_var_params if spec_var_params else params
    param_sig = " ".join(f"({p['param_name']} : {p['param_type']})" for p in _sig_params)
    param_args = " ".join(p["param_name"] for p in _sig_params)
    lambda_wildcards = " ".join("_" for _ in _sig_params)

    # Try to derive precond/postcond from the extracted spec let.
    # The spec let is the one whose extra param type matches return_type.
    _spec_let_name, _result_var, _spec_let_body = find_spec_let(extracted_lets, return_type)

    if _result_var and _spec_let_body:
        _precond_parts, _postcond_raw = extract_precond_and_postcond(
            _spec_let_body, _result_var
        )

        # In the postcondition body:
        #   1. Rename result_var → "result"
        #   2. Extracted non-spec defs need explicit spec params; wrap in parens
        #      to keep prefix operators (¬) correct.
        _spec_param_names = " ".join(p["param_name"] for p in spec_var_params)
        _postcond_body = re.sub(
            r"\b" + re.escape(_result_var) + r"\b", "result", _postcond_raw
        )
        # Only substitute (def_name spec_params) for defs whose body
        # actually references at least one spec param — defs that don't use
        # spec params (e.g. pure constants) are accessible as-is.
        for _n, _, _body in extracted_lets:
            if _n == _spec_let_name:
                continue
            _uses_params = bool(spec_var_params) and any(
                re.search(r"\b" + re.escape(p["param_name"]) + r"\b", _body)
                for p in spec_var_params
            )
            if _uses_params:
                _postcond_body = re.sub(
                    r"\b" + re.escape(_n) + r"\b",
                    f"({_n} {_spec_param_names})",
                    _postcond_body,
                )

        # If no precond found inside the spec let, try the remaining body
        # (e.g. "number > 0 → (∃ result, impl ... = result ∧ spec result)").
        # Segments that don't mention "impl" are preconditions.
        if not _precond_parts and _remaining_spec_body:
            _rem_segs = split_on_implication_arrow(_remaining_spec_body)
            for _seg in _rem_segs[:-1]:
                if not re.search(r"\bimpl\b", _seg):
                    _precond_parts.append(_seg.strip())
                else:
                    break

        if _precond_parts:
            _precond_body = " ∧\n  ".join(f"({p})" for p in _precond_parts) if len(_precond_parts) > 1 else _precond_parts[0]
        else:
            _precond_body = "True"

        def _indent(text: str) -> str:
            return "\n".join("  " + l if l.strip() else l for l in text.splitlines())

        # If the postcondition body calls the implementation itself (recursive spec),
        # the extracted body won't typecheck — fall back to the delegate form.
        _postcond_calls_impl = bool(
            re.search(r"\b(?:implementation|impl)\b", _postcond_body)
        )

        precond_def = f"def precondition {param_sig} : Prop :=\n{_indent(_precond_body)}"
        if _postcond_calls_impl:
            postcond_def = (
                f"def postcondition {param_sig} (result : {return_type}) :=\n"
                f"  problem_spec (fun {lambda_wildcards} => result) {param_args}"
            )
        else:
            postcond_def = (
                f"def postcondition {param_sig} (result : {return_type}) :=\n"
                f"{_indent(_postcond_body)}"
            )
    else:
        # Fallback: precondition = True, postcondition delegates to problem_spec
        precond_def = f"def precondition {param_sig} : Prop :=\n  True"
        postcond_def = (
            f"def postcondition {param_sig} (result : {return_type}) :=\n"
            f"  problem_spec (fun {lambda_wildcards} => result) {param_args}"
        )

    # ── Test cases ────────────────────────────────────────────────────────────
    metadata = problem.problem_spec_metadata
    tests = metadata.test_cases if metadata else []
    test_lines: list[str] = []

    for i, test in enumerate(tests, 1):
        inp = test.get("input")
        # Some CLEVER problems use 'output' instead of 'expected_output'
        expected = test.get("expected_output") if "expected_output" in test else test.get("output")

        # Some multi-param inputs are encoded as a Python tuple string e.g. "([1,2], 5)"
        if isinstance(inp, str) and len(params) > 1:
            try:
                parsed = ast.literal_eval(inp)
                if isinstance(parsed, (tuple, list)) and len(parsed) == len(params):
                    inp = list(parsed)
            except (ValueError, SyntaxError):
                pass

        # Some benchmarks store tuple inputs as a split string list e.g. ['(1', '2)', '(2', '3)']
        # Try to rejoin and reparse as a tuple.
        if (
            isinstance(inp, (list, tuple))
            and len(inp) != len(params)
            and all(isinstance(x, str) for x in inp)
            and len(params) > 1
        ):
            try:
                joined = ", ".join(inp)
                parsed = ast.literal_eval(joined)
                if isinstance(parsed, (tuple, list)) and len(parsed) == len(params):
                    inp = list(parsed)
            except (ValueError, SyntaxError):
                pass

        # Map positional inputs to named parameters.
        # Convention: if there is more than one param, input is a list/tuple of values
        # in parameter order; if there is one param, input is the value itself.
        if len(params) == 1:
            arg_values = [inp]
        elif isinstance(inp, (list, tuple)) and len(inp) == len(params):
            arg_values = list(inp)
        else:
            arg_values = [inp] + [None] * (len(params) - 1)

        for p, val in zip(params, arg_values):
            val_str = python_to_lean(val, p["param_type"])
            test_lines.append(f"def test{i}_{p['param_name']} : {p['param_type']} := {val_str}")

        exp_str = python_to_lean(expected, return_type)
        test_lines.append(f"def test{i}_Expected : {return_type} := {exp_str}")
        test_lines.append("")

    # ── Assemble ──────────────────────────────────────────────────────────────
    parts: list[str] = [
        STANDARD_HEADER,
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

    # ── Variable declarations + extracted let defs ────────────────────────────
    if extracted_lets:
        var_sig = " ".join(f"({p['param_name']} : {p['param_type']})" for p in spec_var_params)
        for name, extra_params, let_body in extracted_lets:
            if name == _spec_let_name:  # the spec let becomes postcondition; skip
                continue
            _uses_spec_params = bool(spec_var_params) and any(
                re.search(r"\b" + re.escape(p["param_name"]) + r"\b", let_body)
                for p in spec_var_params
            )
            if _uses_spec_params:
                full_params = var_sig + (" " + extra_params if extra_params else "")
            else:
                full_params = extra_params
            def_header = f"def {name} {full_params} :=" if full_params else f"def {name} :="
            parts.append(def_header)
            for line in let_body.splitlines():
                parts.append("  " + line if line.strip() else line)
            parts.append("")

    if ground_truth_spec:
        parts += [ground_truth_spec, ""]

    decidable_inst = (
        f"instance instDecidablePrecond {param_sig} : Decidable (precondition {param_args}) := by\n"
        f"  unfold precondition\n"
        f"  infer_instance"
    )

    spec_middle = [precond_def, ""]
    if include_decidable:
        spec_middle += [decidable_inst, ""]
    spec_middle += [postcond_def, ""]

    parts += spec_middle + [
        "end Specs",
        "",
    ]

    # ── Impl section ──────────────────────────────────────────────────────────
    impl_sig = impl_sig  # already stripped above
    impl_body = (problem.implementation or "").strip()
    if impl_sig and impl_body:
        impl_def = f"{impl_sig}\n{impl_body}"
        parts += [
            "section Impl",
            "",
            impl_def,
            "",
            "end Impl",
            "",
        ]

    parts += [
        "section TestCases",
        "",
    ]
    parts += test_lines
    parts += ["end TestCases"]

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


def build_and_check_decidable(problem, out: Path, build_dir: str) -> bool:
    """Write file with Decidable instance, build it, fall back without if it fails.
    Returns True if the instance was kept, False if it was dropped.
    """
    module = _output_file_to_module(str(out), build_dir)

    out.write_text(build_lean_file(problem, include_decidable=True), encoding="utf-8")
    result = subprocess.run(
        ["lake", "build", module],
        cwd=build_dir, capture_output=True, text=True,
    )

    if result.returncode == 0 or not _decidable_failed(result.stdout, result.stderr):
        return True

    out.write_text(build_lean_file(problem, include_decidable=False), encoding="utf-8")
    return False


# ─── Sampler ──────────────────────────────────────────────────────────────────

def _build_sampler_section(params: list[dict], temp_file: str, n: int = 15) -> str:
    """Build a `run_elab do` section that samples valid inputs and writes them to temp_file."""
    param_call = " ".join(p["param_name"] for p in params)

    sample_lines = [
        f"    let {p['param_name']} ← Plausible.Gen.run "
        f"(Plausible.SampleableExt.interpSample ({p['param_type']})) 20"
        for p in params
    ]

    param_repr_lines = [
        "      lines := lines.push s!\"LOOM_PARAM_" + p["param_name"] + "={repr " + p["param_name"] + "}\""
        for p in params
    ]

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
        f"      let result := implementation {param_call}",
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


def _parse_sampler_file(content: str, params: list[dict]) -> list[dict]:
    """Parse the sampler output into dicts {param_name: lean_literal, '__result__': val}.

    Handles multi-line repr values: lines that don't start with a LOOM keyword
    are treated as continuations of the previous value.
    """
    results = []
    lines = content.splitlines()
    i = 0
    while i < len(lines):
        if lines[i].strip() == "LOOM_START":
            entry: dict = {}
            i += 1
            current_key: str | None = None  # "LOOM_PARAM_<name>" or "LOOM_RESULT"
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
                    # Continuation of a multi-line repr value
                    entry[current_key] += stripped
                i += 1
            if all(p["param_name"] in entry for p in params) and "__result__" in entry:
                results.append(entry)
            i += 1  # skip LOOM_END
        else:
            i += 1
    return results


def generate_sampled_tests(params: list[dict], _return_type: str, out: Path,
                            build_dir: str, n: int = 15) -> list[dict]:
    """Append a Lean sampler section to `out`, build it, parse the temp file.

    Returns a list of sample dicts (param -> lean literal, plus '__result__').
    Always restores `out` to its original content.
    """
    temp_file = f"/tmp/loom_clever_sampler_{uuid.uuid4().hex}.txt"
    sampler_code = _build_sampler_section(params, temp_file, n)

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
            samples = _parse_sampler_file(tmp.read_text(encoding="utf-8"), params)
            tmp.unlink(missing_ok=True)
    finally:
        out.write_text(original, encoding="utf-8")

    return samples


def _append_sampled_test_cases(lean_content: str, samples: list[dict],
                                params: list[dict], return_type: str,
                                existing_count: int) -> str:
    """Insert sampled test case defs before `end TestCases`."""
    if not samples:
        return lean_content

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
        description="Convert a CLEVER problem to a spec lean file for PBT"
    )
    parser.add_argument("--id", required=True, type=int,
                        help="CLEVER problem index (0-based), e.g. 0")
    parser.add_argument("--output-file", required=True,
                        help="Output .lean file path")
    parser.add_argument("--build-dir",
                        help="If given, run lake build to execute the sampler")
    parser.add_argument("--sample", type=int, default=0,
                        help="If > 0 and --build-dir is set, sample this many extra "
                             "test cases by running the implementation via Plausible Gen")
    args = parser.parse_args()

    try:
        problem = load_clever_problem(args.id)
    except (ValueError, FileNotFoundError) as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    out = Path(args.output_file)
    out.parent.mkdir(parents=True, exist_ok=True)

    if args.build_dir:
        kept = build_and_check_decidable(problem, out, args.build_dir)
        status = "with Decidable instance" if kept else "WITHOUT Decidable instance (synthesis failed)"
        print(f"Written: {out}  [{status}]")

        if kept and args.sample > 0 and problem.implementation:
            impl_sig = (problem.implementation_signature or "").strip()
            params, return_type = parse_impl_signature(impl_sig)
            existing = len((problem.problem_spec_metadata.test_cases
                            if problem.problem_spec_metadata else None) or [])
            print(f"  Sampling {args.sample} extra test cases via Plausible Gen...")
            samples = generate_sampled_tests(params, return_type, out, args.build_dir, n=args.sample)
            if samples:
                content = out.read_text(encoding="utf-8")
                content = _append_sampled_test_cases(content, samples, params, return_type, existing)
                out.write_text(content, encoding="utf-8")
                print(f"  Added {len(samples)} sampled test cases")
            else:
                print("  No sampled test cases generated (sampler produced no output)")
    else:
        out.write_text(build_lean_file(problem), encoding="utf-8")
        print(f"Written: {out}")


if __name__ == "__main__":
    main()
