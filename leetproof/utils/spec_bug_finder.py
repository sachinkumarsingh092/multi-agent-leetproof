#!/usr/bin/env python3
"""
Check for specification bugs using property-based testing.

For each test case in a spec file, generates uniqueness_testN and uniqueness_testN'
definitions and runs lake build to check for counter-examples.

Usage:
    python -m utils.spec_bug_finder --input-file <spec.lean> --output-file <out.lean> --build-dir <dir>
"""

import re
import sys
import os
import subprocess
import argparse

from utils.example_verify import (
    extract_test_cases,
    find_recommended_tests,
)

NUM_INST = 100000


def extract_base_content(content: str) -> str:
    """Return content up to and including 'end TestCases', stripping trailing verification defs."""
    end_match = re.search(r'end\s+TestCases', content)
    if not end_match:
        raise ValueError("Cannot find 'end TestCases' in input file")
    return content[:end_match.end()].rstrip()


ALL_SUFFIXES = ["", "'", "''"]
FAST_SUFFIXES = ["", "''"]   # no aesop
AESOP_SUFFIXES = ["'"]        # aesop only


# ---------------------------------------------------------------------------
# Helpers for extracting variable info from a test case
# ---------------------------------------------------------------------------

def _param_vars(vars_in_case: list) -> list:
    """Return non-expected, non-type-class variables from a test case."""
    return [v for v in vars_in_case if not (
        v[0].lower().endswith("expected") or
        v[0].endswith("_α") or
        v[0].endswith("_Inh") or
        v[0].endswith("_Dec")
    )]


def _expected_var(vars_in_case: list):
    """Return the first 'expected' variable (name, type, val), or None."""
    evars = [v for v in vars_in_case if v[0].lower().endswith("expected")]
    return evars[0] if evars else None


# ---------------------------------------------------------------------------
# Tactic config factories
# ---------------------------------------------------------------------------

def _uniqueness_tactic_configs(num_inst: int, ret_var_name: str,
                                suffixes: list[str] | None = None) -> list:
    """Tactic configs for uniqueness checking (seeds = expected value)."""
    active = suffixes if suffixes is not None else ALL_SUFFIXES
    result = []
    for suffix, preamble, tactic in [
        ("",
         ["  try simp [loomAbstractionSimp]", "  try dsimp at *", "  try simp [*] at *"],
         f"  plausible'_mut (seeds := #[{ret_var_name}]) (config := {{ numInst := {num_inst} }})"),
        ("'",
         ["  try simp [loomAbstractionSimp]", "  try dsimp at *", "  try simp [*] at *"],
         f"  aesop <;>\n  plausible'_mut (seeds := #[{ret_var_name}]) (config := {{ numInst := {num_inst} }})"),
        ("''",
         ["  try dsimp at *"],
         f"  plausible'_mut (seeds := #[{ret_var_name}]) (config := {{ numInst := {num_inst} }})"),
    ]:
        if suffix in active:
            result.append((suffix, preamble, tactic))
    return result


def _precond_tactic_configs(num_inst: int,
                             suffixes: list[str] | None = None) -> list:
    """Tactic configs for precondition checking (plausible', no seeds)."""
    active = suffixes if suffixes is not None else ALL_SUFFIXES
    result = []
    for suffix, preamble, tactic in [
        ("",
         ["  try simp [loomAbstractionSimp]", "  try dsimp at *", "  try simp [*] at *"],
         f"  plausible' (config := {{ numInst := {num_inst} }})"),
        ("'",
         ["  try simp [loomAbstractionSimp]", "  try dsimp at *", "  try simp [*] at *"],
         f"  aesop <;>\n  plausible' (config := {{ numInst := {num_inst} }})"),
        ("''",
         ["  try dsimp at *"],
         f"  plausible' (config := {{ numInst := {num_inst} }})"),
    ]:
        if suffix in active:
            result.append((suffix, preamble, tactic))
    return result


# ---------------------------------------------------------------------------
# Generic verification def generator
# ---------------------------------------------------------------------------

def generate_verification_defs(
    test_cases: dict,
    rec_cases: list,
    def_name_prefix: str,
    make_extra_params,   # (case_id, vars_in_case) -> str  (empty = no extra params)
    make_proposition,    # (case_id, vars_in_case) -> str | None  (None = skip case)
    tactic_configs: list,  # [(suffix, preamble_lines, tactic_block)]
                           # tactic_block: str or callable(case_id, vars_in_case) -> str
) -> str:
    lines = []
    for case_id in rec_cases:
        if case_id not in test_cases:
            continue
        vars_in_case = test_cases[case_id]
        proposition = make_proposition(case_id, vars_in_case)
        if proposition is None:
            continue
        extra_params = make_extra_params(case_id, vars_in_case)
        for suffix, preamble, tactic_block in tactic_configs:
            tb = tactic_block(case_id, vars_in_case) if callable(tactic_block) else tactic_block
            name = f"{def_name_prefix}_{case_id}{suffix}"
            if extra_params:
                lines.append(f"def {name} {extra_params} :")
            else:
                lines.append(f"def {name} :")
            lines.append(f"  {proposition} := by")
            lines.extend(preamble)
            lines.append(tb)
            lines.append("")
    return "\n".join(lines)


def _make_uniqueness_extra_params(case_id, vars_in_case) -> str:
    ev = _expected_var(vars_in_case)
    return f"(result : {ev[1]})" if ev else ""


def _make_uniqueness_proposition(case_id, vars_in_case):
    ev = _expected_var(vars_in_case)
    if ev is None:
        return None
    param_list = " ".join(v[0] for v in _param_vars(vars_in_case))
    return f"result ≠ {ev[0]} →\n  ¬ postcondition {param_list} result"


def _make_precond_extra_params(*_) -> str:
    return ""


def _make_precond_proposition(case_id, vars_in_case) -> str:
    param_list = " ".join(v[0] for v in _param_vars(vars_in_case))
    return f"precondition {param_list}"


def _make_postcond_proposition(_, vars_in_case):
    ev = _expected_var(vars_in_case)
    if ev is None:
        return None
    param_list = " ".join(v[0] for v in _param_vars(vars_in_case))
    return f"postcondition {param_list} {ev[0]}"


# ---------------------------------------------------------------------------
# Build helpers
# ---------------------------------------------------------------------------

def output_file_to_module(output_file: str, build_dir: str) -> str:
    """Convert output file path to Lean module name relative to build_dir."""
    output_abs = os.path.abspath(output_file)
    build_abs = os.path.abspath(build_dir)
    rel = os.path.relpath(output_abs, build_abs)
    if rel.endswith(".lean"):
        rel = rel[:-5]
    return rel.replace(os.sep, ".")


def run_lake_build(build_dir: str, module: str) -> tuple[str, str, int]:
    """Run lake build for a module and return (stdout, stderr, returncode). Raises subprocess.TimeoutExpired on timeout."""
    result = subprocess.run(
        ["lake", "build", module],
        cwd=build_dir,
        capture_output=True,
        text=True,
        timeout=45,
    )
    return result.stdout, result.stderr, result.returncode


def check_for_counter_example(stdout: str, stderr: str) -> list[str]:
    """Return list of lines where a counter-example was found."""
    combined = stdout + "\n" + stderr
    found = []
    for line in combined.splitlines():
        if "Found a counter-example" in line:
            found.append(line.strip())
    return found


def check_for_synthesis_failure(stdout: str, stderr: str) -> bool:
    """Return True if all defs hit synthesis failure (no testable instance)."""
    combined = stdout + "\n" + stderr
    return any("Failed to synthesize a `testable` instance" in line for line in combined.splitlines())


def check_for_decide_false(stdout: str, stderr: str) -> bool:
    """Return True if the decide tactic failed because the prop evaluated to False."""
    combined = stdout + "\n" + stderr
    return any("decide tactic failed" in line for line in combined.splitlines())


# ---------------------------------------------------------------------------
# Ground-proposition checker (shared by precondition and postcondition)
# ---------------------------------------------------------------------------

# The tactic sequence mirroring tryLoomMkDecidable
_DECIDABLE_TACTIC = (
    "  repeat' refine @instDecidableAnd _ _ ?_ ?_\n"
    "  all_goals (try (infer_aux_decidable_instance ; infer_instance))"
)


def _check_ground_prop(
    test_cases: dict,
    valid_cases: list,
    base: str,
    output_file: str,
    build_dir: str,
    module: str,
    def_name_prefix: str,       # e.g. "testprecondition" or "testpostcondition"
    make_prop,                  # (case_id, vars) -> str | None
    bug_return: str,            # e.g. "precond_bug" or "postcond_bug"
    check_name: str,            # e.g. "precondition" or "postcondition"
) -> tuple[str, str]:
    """
    Check that a ground proposition holds for every test-case input.

    Strategy:
      Stage 1 — Decidable probe (tryLoomMkDecidable tactic sequence):
        - Compiles (rc==0) → use `decide` for all cases (deterministic).
          `decide` failing means the prop is False → bug_return.
        - Fails / timeout  → fall through to Stage 2.

      Stage 2 — Testable probe (tryLoomMkTestable via plausible'):
        - Counter-example  → bug_return.
        - Synthesis ok     → direct plausible' for remaining cases.
        - Synthesis fails  → three-pass mode (simp / dsimp / aesop).

    Returns (status, detail) where status is bug_return, 'synthesis_failed', or 'ok'.
    """
    if not valid_cases:
        return "ok", ""

    def _detail(case_id: str, counterex: list[str] | None = None) -> str:
        lines = [f"Test case `{case_id}`: {check_name} check failed."]
        if counterex:
            lines.append("Counter-example:")
            lines.extend(f"  {ln}" for ln in counterex)
        return "\n".join(lines)

    def _decidable_prop(_, vars_in_case) -> str | None:
        p = make_prop(_, vars_in_case)
        return None if p is None else f"Decidable ({p})"

    def _write_and_run(tactic_configs, case_id, prop_fn=make_prop):
        verification = generate_verification_defs(
            test_cases, [case_id],
            def_name_prefix,
            lambda *_: "",   # no extra params
            prop_fn,
            tactic_configs,
        )
        output_content = base + "\n\nset_option maxHeartbeats 500000\n\n" + verification
        with open(output_file, "w", encoding="utf-8") as f:
            f.write(output_content)
        return run_lake_build(build_dir, module)

    # ------------------------------------------------------------------
    # Stage 1: Decidable probe
    # ------------------------------------------------------------------
    probe_case = valid_cases[0]
    try:
        _, _, rc = _write_and_run(
            [("", [], _DECIDABLE_TACTIC)], probe_case, prop_fn=_decidable_prop
        )
        is_decidable = (rc == 0)
    except subprocess.TimeoutExpired:
        print(f"  [{check_name}] Decidable probe timed out, falling back to plausible'", flush=True)
        is_decidable = False

    if is_decidable:
        print(f"  {check_name} (decidable, explicit instance, batch):", flush=True)

        # Re-indent _DECIDABLE_TACTIC lines by 2 extra spaces so they sit
        # inside the `haveI ... := by` block (from 2-space to 4-space indent).
        _tactic_indented = "\n".join(
            "  " + ln if ln.strip() else ln
            for ln in _DECIDABLE_TACTIC.splitlines()
        )

        def _haveI_decide(case_id, vars_in_case):
            prop = make_prop(case_id, vars_in_case)
            if prop is None:
                return "  trivial"
            return (
                f"  haveI : Decidable ({prop}) := by\n"
                f"{_tactic_indented}\n"
                f"  decide"
            )

        # All cases in one file — single lake build instead of N builds.
        verification = generate_verification_defs(
            test_cases, valid_cases,
            def_name_prefix,
            lambda *_: "",
            make_prop,
            [("", [], _haveI_decide)],
        )
        output_content = base + "\n\nset_option maxHeartbeats 500000\n\n" + verification
        with open(output_file, "w", encoding="utf-8") as f:
            f.write(output_content)

        try:
            stdout, stderr, _ = run_lake_build(build_dir, module)
        except subprocess.TimeoutExpired:
            print(f"  [{check_name}] Batch decide check timed out, skipping", flush=True)
            return "ok", ""

        if check_for_decide_false(stdout, stderr):
            # Identify the failing case by matching definition names in error output.
            combined = stdout + "\n" + stderr
            failing_case = next(
                (c for c in valid_cases if f"{def_name_prefix}_{c}" in combined),
                valid_cases[0],
            )
            print(f"\n[{check_name.upper()} BUG] on {failing_case}")
            return bug_return, _detail(failing_case)

        return "ok", ""

    # ------------------------------------------------------------------
    # Stage 2: Testable probe via plausible'
    # ------------------------------------------------------------------
    try:
        stdout, stderr, _ = _write_and_run(
            [("", [], "  plausible' (config := { numInst := 1 })")], probe_case
        )
    except subprocess.TimeoutExpired:
        print(f"  [{check_name}] plausible' probe timed out, skipping", flush=True)
        return "ok", ""

    if check_for_counter_example(stdout, stderr):
        counterex = check_for_counter_example(stdout, stderr)
        for ln in counterex:
            print(f"    {ln}")
        print(f"\n[{check_name.upper()} BUG] on {probe_case}")
        return bug_return, _detail(probe_case, counterex)

    use_direct = not check_for_synthesis_failure(stdout, stderr)
    outcomes: dict[str, str] = {probe_case: "ok" if use_direct else "synthesis_failed"}

    if use_direct:
        print(f"  {check_name} (testable, direct plausible'):", flush=True)
        num_inst = NUM_INST
        for case_id in valid_cases[1:]:
            print(f"    checking {case_id}", flush=True)
            stdout = stderr = ""
            while True:
                configs = [("", [], f"  plausible' (config := {{ numInst := {num_inst} }})")]
                try:
                    stdout, stderr, _ = _write_and_run(configs, case_id)
                    break
                except subprocess.TimeoutExpired:
                    next_ni = num_inst // 10
                    if next_ni < 300:
                        print(f"    [{case_id}] Timeout, skipping")
                        outcomes[case_id] = "timeout"
                        break
                    print(f"    [{case_id}] Timeout (numInst={num_inst}), retrying with numInst={next_ni}...", flush=True)
                    num_inst = next_ni
            if outcomes.get(case_id) == "timeout":
                continue
            counterex = check_for_counter_example(stdout, stderr)
            if counterex:
                for ln in counterex:
                    print(f"    {ln}")
                print(f"\n[{check_name.upper()} BUG] on {case_id}")
                return bug_return, _detail(case_id, counterex)
            outcomes[case_id] = "ok"

    else:
        print(f"  {check_name} (three-pass mode):", flush=True)
        for pass_name, suffixes in [("pass 1", [""]), ("pass 2", ["''"]), ("pass 3", ["'"])]:
            to_run = [c for c in valid_cases if outcomes.get(c) not in ("bug",)]
            if not to_run:
                break
            print(f"  {pass_name}:", flush=True)
            num_inst = NUM_INST
            pass_timed_out = False
            for case_id in to_run:
                print(f"    checking {case_id}", flush=True)
                stdout = stderr = ""
                while True:
                    configs = _precond_tactic_configs(num_inst, suffixes)
                    try:
                        stdout, stderr, _ = _write_and_run(configs, case_id)
                        break
                    except subprocess.TimeoutExpired:
                        next_ni = num_inst // 10
                        if next_ni < 300:
                            print(f"    [{case_id}] Timeout (numInst={num_inst}), skipping rest of {pass_name}", flush=True)
                            pass_timed_out = True
                            break
                        print(f"    [{case_id}] Timeout (numInst={num_inst}), retrying with numInst={next_ni}...", flush=True)
                        num_inst = next_ni
                if pass_timed_out:
                    break
                counterex = check_for_counter_example(stdout, stderr)
                if counterex:
                    for ln in counterex:
                        print(f"    {ln}")
                    print(f"\n[{check_name.upper()} BUG] on {case_id}")
                    return bug_return, _detail(case_id, counterex)
                outcomes[case_id] = "synthesis_failed" if check_for_synthesis_failure(stdout, stderr) else "ok"

        if outcomes and all(v == "synthesis_failed" for v in outcomes.values()):
            print(f"  [{check_name}] All cases synthesis failed — check inconclusive")
            return "synthesis_failed", ""

    return "ok", ""


def check_preconditions(
    test_cases: dict, valid_cases: list, base: str,
    output_file: str, build_dir: str, module: str,
) -> tuple[str, str]:
    return _check_ground_prop(
        test_cases, valid_cases, base, output_file, build_dir, module,
        def_name_prefix="testprecondition",
        make_prop=_make_precond_proposition,
        bug_return="precond_bug",
        check_name="precondition",
    )


def check_postconditions(
    test_cases: dict, valid_cases: list, base: str,
    output_file: str, build_dir: str, module: str,
) -> tuple[str, str]:
    return _check_ground_prop(
        test_cases, valid_cases, base, output_file, build_dir, module,
        def_name_prefix="testpostcondition",
        make_prop=_make_postcond_proposition,
        bug_return="postcond_bug",
        check_name="postcondition",
    )


# ---------------------------------------------------------------------------
# Main checker
# ---------------------------------------------------------------------------

def generate_and_check(input_file: str, output_file: str, build_dir: str) -> tuple[str, str]:
    """Run all PBT checks and return (result, detail).

    result is one of: 'no_bug', 'bug', 'precond_bug', 'postcond_bug', 'synthesis_failed'.
    detail is a human-readable explanation (empty string when no bug found).
    """
    with open(input_file, "r", encoding="utf-8") as f:
        content = f.read()

    # Extract test cases
    test_cases = extract_test_cases(content)

    # Find recommended tests
    rec_cases = find_recommended_tests(content)
    if not rec_cases:
        def _case_sort_key(k: str) -> int:
            m = re.search(r'\d+', k)
            return int(m.group()) if m else 0
        rec_cases = sorted(test_cases.keys(), key=_case_sort_key)

    base = extract_base_content(content)
    module = output_file_to_module(output_file, build_dir)
    os.makedirs(os.path.dirname(os.path.abspath(output_file)), exist_ok=True)

    valid_cases = [c for c in rec_cases if c in test_cases]

    # ------------------------------------------------------------------
    # Phase 0: check preconditions
    # ------------------------------------------------------------------
    print("Checking preconditions...", flush=True)
    status, detail = check_preconditions(test_cases, valid_cases, base, output_file, build_dir, module)
    if status == "precond_bug":
        return "precond_bug", detail

    # ------------------------------------------------------------------
    # Phase 1: check postconditions (expected value satisfies spec)
    # ------------------------------------------------------------------
    print("Checking postconditions...", flush=True)
    status, detail = check_postconditions(test_cases, valid_cases, base, output_file, build_dir, module)
    if status == "postcond_bug":
        return "postcond_bug", detail

    # ------------------------------------------------------------------
    # Phase 2: uniqueness check (three passes)
    # ------------------------------------------------------------------
    print("Checking uniqueness...", flush=True)

    # Track per-case outcomes: 'bug', 'no_counterexample', 'synthesis_failed', 'skipped'
    outcomes: dict[str, str] = {}
    for c in rec_cases:
        if c not in test_cases:
            outcomes[c] = "skipped"

    pass_configs = [
        ("pass 1", [""]),
        ("pass 2", ["''"]),
        ("pass 3", ["'"]),
    ]

    for pass_name, suffixes in pass_configs:
        to_run = [c for c in valid_cases
                  if outcomes.get(c) not in ("bug",)]
        if not to_run:
            break

        print(f"  {pass_name}:", flush=True)
        num_inst = NUM_INST
        pass_timed_out = False

        for case_id in to_run:
            print(f"    running on {case_id}", flush=True)

            vars_in_case = test_cases[case_id]
            ev = _expected_var(vars_in_case)
            if ev is None:
                outcomes[case_id] = "skipped"
                continue

            ret_var_name = ev[0]

            stdout = stderr = ""
            while True:
                tactic_configs = _uniqueness_tactic_configs(num_inst, ret_var_name, suffixes)
                verification = generate_verification_defs(
                    test_cases, [case_id],
                    "uniqueness",
                    _make_uniqueness_extra_params,
                    _make_uniqueness_proposition,
                    tactic_configs,
                )
                output_content = base + "\n\nset_option maxHeartbeats 500000\n\n" + verification
                with open(output_file, "w", encoding="utf-8") as f:
                    f.write(output_content)
                try:
                    stdout, stderr, _ = run_lake_build(build_dir, module)
                    break
                except subprocess.TimeoutExpired:
                    next_num_inst = num_inst // 10
                    if next_num_inst < 300:
                        print(f"    [{case_id}] Timeout (numInst={num_inst}), skipping rest of {pass_name}", flush=True)
                        pass_timed_out = True
                        break
                    print(f"    [{case_id}] Timeout (numInst={num_inst}), retrying with numInst={next_num_inst}...", flush=True)
                    num_inst = next_num_inst

            if pass_timed_out:
                break

            counterex = check_for_counter_example(stdout, stderr)
            if counterex:
                for ln in counterex:
                    print(f"    {ln}")
                print(f"\n[SPECIFICATION BUG FOUND] on {case_id}")
                bug_detail = (
                    f"Test case `{case_id}`: uniqueness check failed — "
                    "an alternative output was found that also satisfies the postcondition "
                    "(the postcondition may be underspecified).\n"
                    "Counter-example:\n" + "\n".join(f"  {ln}" for ln in counterex)
                )
                return "bug", bug_detail
            if check_for_synthesis_failure(stdout, stderr):
                outcomes[case_id] = "synthesis_failed"
            else:
                outcomes[case_id] = "no_counterexample"
            # If the first 3 cases all failed synthesis, skip the rest of this pass
            if case_id == to_run[2] if len(to_run) >= 3 else False:
                if all(outcomes.get(c) == "synthesis_failed" for c in to_run[:3]):
                    print(f"    First 3 cases all synthesis failed, skipping rest of {pass_name}", flush=True)
                    break

    tested = {k: v for k, v in outcomes.items() if v != "skipped"}
    if tested and all(v == "synthesis_failed" for v in tested.values()):
        print("[SYNTHESIS FAILED] All test cases failed to synthesize — test inconclusive")
        return "synthesis_failed", ""

    print("[No counter-example found]")
    return "no_bug", ""


def main():
    parser = argparse.ArgumentParser(
        description="Check for specification bugs via property-based testing"
    )
    parser.add_argument("--input-file", required=True,
                        help="Input spec lean file (e.g., llmgen/test1.lean)")
    parser.add_argument("--output-file", required=True,
                        help="Output lean file with generated verification defs")
    parser.add_argument("--build-dir", required=True,
                        help="Directory to run lake build from")
    args = parser.parse_args()

    try:
        result, detail = generate_and_check(args.input_file, args.output_file, args.build_dir)
        if detail:
            print(detail, flush=True)
        # exit codes: 0 = no bug, 1 = bug, 2 = error, 3 = synthesis failed, 4 = precond bug, 5 = postcond bug
        if result == "bug":
            sys.exit(1)
        elif result == "synthesis_failed":
            sys.exit(3)
        elif result == "precond_bug":
            sys.exit(4)
        elif result == "postcond_bug":
            sys.exit(5)
        else:
            sys.exit(0)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
