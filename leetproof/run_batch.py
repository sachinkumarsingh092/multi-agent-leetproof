#!/usr/bin/env python3
"""
Run lloom-agent pipeline on a batch of problems defined in JSON.

Usage:
    lloom-agent run-batch tests.json [pipeline options...]
    lloom-agent run-batch tests.json --grade-only

JSON format (generate interactively with ``lloom-agent gen-batch``):
    [
        {"dataset": "mbpp", "id_type": "position", "id": 3},
        {"dataset": "mbpp", "id_type": "mbpp_id", "id": 807},
        {"dataset": "verina", "difficulty": "basic", "id": 15},
        {"dataset": "verina", "difficulty": "advanced", "id": 25, "mode": "pure_lean", "input_file": "path/to/spec.lean"},
        {"dataset": "custom", "id": "my_test", "input_file": "path/to/spec.lean"},
        {"dataset": "mbpp", "id_type": "mbpp_id", "id": 3, "resume": true, "session_name": "..."}
    ]

Per-test run options: "mode", "input_file", "cwd", "options", "session_name", "resume".
Global flags --pure-lean / --pure-dafny apply to all test cases.
"""

import json
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import Any

from config.constants import SESSIONS_DIR
from evals.dataset import DatasetProblem, parse_test_case

# Consistent timestamp per test key within a run
_timestamps: dict[str, str] = {}

DEFAULT_CWD = None
STAGE_ORDER = ["specgen", "codegen", "invgen", "verify"]


# ---------------------------------------------------------------------------
# Session management
# ---------------------------------------------------------------------------

def _find_latest_session(problem: DatasetProblem) -> str | None:
    """Find the latest session directory matching a problem."""
    sessions_dir = Path(problem.cwd) / SESSIONS_DIR
    if not sessions_dir.exists():
        return None
    matches = sorted(sessions_dir.glob(f"{problem.base_name}_*"))
    return matches[-1].name if matches else None


def _session_name(problem: DatasetProblem) -> str:
    """Get or generate session name for a problem."""
    # Resume with explicit session name
    if problem.resume and problem.session_name:
        return problem.session_name

    key = problem.test_key

    # Resume without explicit session name: find latest
    if problem.resume:
        latest = _find_latest_session(problem)
        if latest:
            return latest
        print(f"  No existing session found for {key}, starting fresh")

    base = problem.session_name or key
    if key not in _timestamps:
        _timestamps[key] = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    return f"{base}_{_timestamps[key]}"


# ---------------------------------------------------------------------------
# Result file resolution
# ---------------------------------------------------------------------------

def _result_file(problem: DatasetProblem, session: str | None) -> str | None:
    """Get expected result file path for a problem."""
    name = problem.base_name
    if "unknown" in name:
        return None
    base_path = f"{problem.cwd}/{SESSIONS_DIR}/{session}/" if session else ""
    if problem.mode == "pure_dafny":
        return f"{base_path}Impl_result.json"
    if problem.mode == "pure_lean":
        return f"{base_path}LeanImpl_result.json"
    return f"{base_path}Spec_result.json"


def _load_json(path: str) -> dict | None:
    try:
        p = Path(path)
        return json.loads(p.read_text()) if p.exists() else None
    except Exception as e:
        print(f"  Warning: Could not load {path}: {e}")
        return None


# ---------------------------------------------------------------------------
# Running test cases
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).parent.resolve()
_FROZEN = getattr(sys, 'frozen', False)  # True when running from PyInstaller binary


def _extract_model(global_opts: list[str]) -> str:
    """Extract --model value from options, default 'default'."""
    for i, opt in enumerate(global_opts):
        if opt == "--model" and i + 1 < len(global_opts):
            return global_opts[i + 1]
    return "default"


def _pipeline_args(problem: DatasetProblem, global_opts: list[str]) -> list[str]:
    """Build common pipeline args shared across all modes."""
    session = _session_name(problem)
    args = ["--session-name", session]
    if problem.resume:
        args.append("--resume")
    if problem.options:
        args.extend(problem.options.split())
    args.extend(o for o in global_opts if o not in ("--pure-lean", "--pure-dafny"))
    return args


def _output_subdir(ds: str) -> str:
    """Map dataset name to PascalCase output subdirectory."""
    if not ds:
        return "Custom"
    return {"mbpp": "Mbpp", "verina": "Verina", "custom": "Custom"}.get(ds, ds.title())


def _normalize_model_name(model: str) -> str:
    """Normalize model ID to a clean directory name.

    Strips date suffixes and replaces '-'/'.' with '_'.
    E.g. 'claude-sonnet-4-5-20250929' → 'claude_sonnet_4_5'
         'gpt-5.2-2025-12-11' → 'gpt_5_2'
    """
    import re
    # Strip trailing date suffix (YYYYMMDD or YYYY-MM-DD)
    model = re.sub(r'[-_]?\d{4}-?\d{2}-?\d{2}$', '', model)
    return model.replace('-', '_').replace('.', '_')


def _to_pascal_case(snake_str: str) -> str:
    """Convert snake_case to PascalCase. E.g. 'mbpp_id_291' → 'MbppId291'."""
    return ''.join(part.capitalize() for part in snake_str.split('_'))


def _build_command(problem: DatasetProblem, global_opts: list[str]) -> tuple[list[str] | None, str]:
    """Build the command to run for a problem.

    Returns (cmd, description) on success, (None, error) on failure.
    Side-effects: extracts problem descriptions and creates output directories as needed.
    """
    cwd = problem.cwd
    pure_lean = problem.mode == "pure_lean" or "--pure-lean" in global_opts
    pure_dafny = problem.mode == "pure_dafny" or "--pure-dafny" in global_opts
    model = _extract_model(global_opts)
    pargs = _pipeline_args(problem, global_opts)

    # Resolve subcommand, input_file, output_file depending on mode
    if pure_dafny or pure_lean:
        input_file = problem.input_file
        if not input_file:
            mode = "pure-dafny" if pure_dafny else "pure-lean"
            return None, f"input_file required for {mode} mode"
        from utils.naming import derive_from_spec, OutputTarget
        if pure_dafny:
            subcmd = "dafny-synth"
            output_file = derive_from_spec(input_file, OutputTarget.DAFNY_IMPL)
        else:
            subcmd = "lean-synth"
            output_file = derive_from_spec(input_file, OutputTarget.LEAN_IMPL)
    else:
        subcmd = "pipeline"
        pid = problem.problem_id
        ds = problem.dataset_name()
        if ds in ("mbpp", "verina"):
            input_file, err = problem.extract(cwd)
            if not input_file:
                return None, err
        else:
            input_file = problem.input_file
            if not input_file:
                return None, "Missing 'input_file' for non-mbpp/verina test case"
        output_file = f"llmgen/{_normalize_model_name(model)}/{_output_subdir(ds)}/{_to_pascal_case(pid)}/Spec.lean"
        (Path(cwd) / Path(output_file).parent).mkdir(parents=True, exist_ok=True)

    # Build command — use the binary directly when frozen, otherwise uv run
    if _FROZEN:
        cmd = [sys.executable, subcmd]
    else:
        script = SCRIPT_DIR / {"pipeline": "pipeline.py", "lean-synth": "lean_synth_and_verify.py", "dafny-synth": "dafny_synth.py"}[subcmd]
        cmd = ["uv", "run", "python3", str(script)]
    cmd.extend(["--project", "."])
    if output_file:
        cmd.extend(["--output-file", output_file])
    if input_file:
        cmd.extend(["--input-file", input_file])
    cmd.extend(pargs)
    return cmd, f"Running {subcmd}"


def _run(cmd: list[str], desc: str, cwd: str | None = None) -> int:
    """Run a command, print it, return exit code."""
    print(f"  {desc}")
    if cwd:
        print(f"  CWD: {cwd}")
    print(f"  $ {' '.join(cmd)}")
    return subprocess.run(cmd, capture_output=False, cwd=cwd).returncode


# ---------------------------------------------------------------------------
# Grading
# ---------------------------------------------------------------------------

def _analyze(results: dict) -> dict[str, Any]:
    """Extract pass/fail metrics from a result file."""
    s = {
        "specgen": False, "pbt_result": "",
        "codegen": False, "pbt_status": "NOT_ATTEMPTED",
        "invgen": False, "verify": False,
        "verify_proven": 0, "verify_partial": 0, "verify_total": 0,
        "started_from": None, "failed_at": None,
    }
    if not results:
        return s

    # Find start and failure points
    for stage in STAGE_ORDER:
        if stage in results:
            s["started_from"] = s["started_from"] or stage
    if not s["started_from"]:
        s["started_from"] = "specgen"
        s["failed_at"] = "specgen"
        return s

    start_idx = STAGE_ORDER.index(s["started_from"])
    fail_idx = len(STAGE_ORDER)

    for i, stage in enumerate(STAGE_ORDER):
        if i < start_idx or stage not in results:
            continue
        data = results[stage]
        failed = False
        if stage == "specgen":
            failed = data.get("coach_verdict") == "REJECT"
        elif stage in ("codegen", "invgen"):
            failed = data.get("judge_verdict") == "FAIL"
        if failed:
            fail_idx = i
            s["failed_at"] = stage
            break

    # Extract per-stage metrics
    def _active(stage):
        return stage in results and STAGE_ORDER.index(stage) >= start_idx and STAGE_ORDER.index(stage) < fail_idx

    if "specgen" in results and STAGE_ORDER.index("specgen") >= start_idx:
        sg = results["specgen"]
        s["specgen"] = sg.get("passed", False)
        s["pbt_result"] = sg.get("pbt_result", "")

    if _active("codegen"):
        cg = results["codegen"]
        s["codegen"] = cg.get("testcase_passed", False) is True and cg.get("judge_verdict") == "PASS"
        pbt = cg.get("pbt_status", cg.get("pbt_passed", "NOT_ATTEMPTED"))
        if isinstance(pbt, bool):
            pbt = "ADDED_AND_PASSED" if pbt else "NOT_ATTEMPTED"
        s["pbt_status"] = pbt

    if _active("invgen"):
        s["invgen"] = results["invgen"].get("completed", False)

    if _active("verify"):
        v = results["verify"]
        s["verify"] = v.get("typechecks", False)
        s["verify_proven"] = v.get("goals_proven", 0)
        s["verify_partial"] = v.get("goals_partial", 0)
        s["verify_total"] = v.get("goals_total", 0)

    return s


def _is_passed(s: dict) -> bool:
    return s["specgen"] and s["codegen"] and s["invgen"] and s["verify"]


def _print_report(problems: list[DatasetProblem], use_latest: bool = False):
    print("\n" + "=" * 115)
    print("GRADING REPORT")
    print("=" * 115)

    totals = {k: 0 for k in [
        "n", "specgen", "pbt_bug", "codegen",
        "pbt_pass", "pbt_fail", "invgen", "verify",
        "vg_proven", "vg_partial", "vg_total",
    ]}

    rows = []
    for i, problem in enumerate(problems, 1):
        session = _find_latest_session(problem) if use_latest else _session_name(problem)
        rf = _result_file(problem, session)
        if not rf:
            print(f"  Test case {i}: Cannot determine result file path")
            continue
        results = _load_json(rf)
        if not results:
            print(f"  Test case {i}: No result file found at {rf}")
        s = _analyze(results or {})
        rows.append((i, problem, s))
        totals["n"] += 1

        if s["specgen"]: totals["specgen"] += 1
        if s["pbt_result"] in ("bug", "precond_bug", "postcond_bug"): totals["pbt_bug"] += 1
        if s["codegen"]: totals["codegen"] += 1
        pbt = s["pbt_status"]
        if pbt == "ADDED_AND_PASSED": totals["pbt_pass"] += 1
        elif pbt == "ADDED_COMPILE_FAILED": totals["pbt_fail"] += 1
        if s["invgen"]: totals["invgen"] += 1
        if s["verify"]: totals["verify"] += 1
        totals["vg_proven"] += s["verify_proven"]
        totals["vg_partial"] += s["verify_partial"]
        totals["vg_total"] += s["verify_total"]

    n = totals["n"] or 1
    pct = lambda v: f"{v/n*100:5.1f}%"
    print(f"\nSTATISTICS ({totals['n']}/{len(problems)} analyzed)")
    print("-" * 80)
    print(f"  SpecGen:    {totals['specgen']:3d}/{n:3d} ({pct(totals['specgen'])})  |  PBT bugs: {totals['pbt_bug']}")
    print(f"  CodeGen:    {totals['codegen']:3d}/{n:3d}  |  PBT: {totals['pbt_pass']} passed, {totals['pbt_fail']} failed")
    print(f"  InvGen:     {totals['invgen']:3d}/{n:3d} ({pct(totals['invgen'])})")
    print(f"  Verify:     {totals['verify']:3d}/{n:3d} ({pct(totals['verify'])})")
    if totals["vg_total"]:
        print(f"              {totals['vg_proven']}/{totals['vg_total']} goals proven, {totals['vg_partial']} partial")

    print(f"\nDETAILED RESULTS")
    hdr = f"{'#':>4} | {'Dataset':20s} | {'Spec':^8} | {'Code':^10} | {'Inv':^4} | {'Verify':^12}"
    print("-" * len(hdr))
    print(hdr)
    print("-" * len(hdr))

    for i, problem, s in rows:
        pbt_ch = {"no_bug": "ok", "synthesis_failed": "?", "bug": "BUG",
                  "precond_bug": "PRE", "postcond_bug": "POST", "": "-"}.get(s["pbt_result"], s["pbt_result"])
        spec = f"{'Y' if s['specgen'] else '-'} {pbt_ch}"

        pbt_ch2 = {"ADDED_AND_PASSED": "P", "ADDED_COMPILE_FAILED": "F", "NOT_ADDED": "N"}.get(s["pbt_status"], "-")
        code = f"{'Y' if s['codegen'] else '-'} pbt:{pbt_ch2}"
        inv = "Y" if s["invgen"] else "-"

        vp, vpa, vt = s["verify_proven"], s["verify_partial"], s["verify_total"]
        if s["verify"]:
            ver = f"Y {vp}/{vt}"
        elif vt > 0:
            ver = f"- {vp}+{vpa}/{vt}"
        else:
            ver = "-"

        info = ""
        if s.get("started_from") and s["started_from"] != "specgen":
            info += f" [from:{s['started_from']}]"
        if s.get("failed_at"):
            info += f" [fail:{s['failed_at']}]"

        print(f"{i:4d} | {problem.label:20s} | {spec:^8s} | {code:^10s} | {inv:^4s} | {ver:12s}{info}")

    print("-" * len(hdr))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    if len(sys.argv) < 2 or "--help" in sys.argv or "-h" in sys.argv:
        print("Usage: lloom-agent run-batch --project <lean-project> <tests.json> [pipeline options...]")
        print("       lloom-agent run-batch --project <lean-project> --grade-only <tests.json>")
        print()
        print("Run a batch of problems defined in a JSON file.")
        print()
        print("Required:")
        print("  --project <path>    Lean project directory (containing lakefile.lean)")
        print("  <tests.json>        JSON file with test case definitions")
        print()
        print("Options:")
        print("  --grade-only        Grade existing results without re-running")
        print("  --pure-lean         Use standalone Lean synthesis for all tests")
        print("  --pure-dafny        Use standalone Dafny synthesis for all tests")
        print("  --provider <name>   LLM provider (passed to pipeline)")
        print("  --model <name>      Model name (passed to pipeline)")
        print("  -h, --help          Show this help message")
        sys.exit(0)

    # Extract --project from argv (required, used as default cwd for test cases)
    argv = sys.argv[1:]
    project_dir = DEFAULT_CWD
    filtered_argv = []
    i = 0
    while i < len(argv):
        if argv[i] == "--project" and i + 1 < len(argv):
            project_dir = argv[i + 1]
            i += 2
        elif argv[i].startswith("--project="):
            project_dir = argv[i].split("=", 1)[1]
            i += 1
        else:
            filtered_argv.append(argv[i])
            i += 1

    if not project_dir:
        print("Error: --project is required")
        print("Usage: lloom-agent run-batch --project <lean-project> <tests.json> [pipeline options...]")
        sys.exit(1)

    grade_only = filtered_argv[0] == "--grade-only" if filtered_argv else False
    if grade_only:
        if len(filtered_argv) < 2:
            print("Error: --grade-only requires a JSON file")
            sys.exit(1)
        args = filtered_argv[1:]
    else:
        args = filtered_argv

    json_file = args[0] if args else None
    if not json_file or not Path(json_file).exists():
        print(f"JSON file not found: {json_file}")
        sys.exit(1)

    try:
        test_cases = json.loads(Path(json_file).read_text())
    except Exception as e:
        print(f"Error reading {json_file}: {e}")
        sys.exit(1)

    if not isinstance(test_cases, list):
        print("JSON file should contain an array of test cases")
        sys.exit(1)

    # Parse raw dicts into typed DatasetProblem objects
    # Default cwd to --project for entries that don't specify one
    problems: list[DatasetProblem] = []
    for tc in test_cases:
        tc.setdefault("dataset", "")
        tc.setdefault("cwd", project_dir)
        problems.append(parse_test_case(tc))

    pipeline_opts = args[1:]

    if grade_only:
        print(f"Grading {len(problems)} test cases from {json_file}")
        _print_report(problems, use_latest=True)
        return

    print(f"Running {len(problems)} test cases from {json_file}")
    if pipeline_opts:
        print(f"Options: {' '.join(pipeline_opts)}")
    print()

    failed = []
    for i, problem in enumerate(problems, 1):
        resuming = problem.resume
        print(f"[{i}/{len(problems)}] {problem.label}{' (resuming)' if resuming else ''}")
        print(f"  Session: {_session_name(problem)}")

        cmd, desc = _build_command(problem, pipeline_opts)
        if not cmd:
            print(f"  ERROR: {desc}")
            failed.append((i, problem))
            continue

        _run(cmd, desc, cwd=problem.cwd)

        session = _session_name(problem)
        rf = _result_file(problem, session)
        if not rf or not _is_passed(_analyze(_load_json(rf) or {})):
            failed.append((i, problem))
        print()

    total = len(problems)
    passed = total - len(failed)
    print(f"Summary: {passed}/{total} passed")

    if failed:
        print("Failed:")
        for num, problem in failed:
            print(f"  {num}: {problem.label}")
    else:
        print("All test cases passed!")

    _print_report(problems, use_latest=False)


if __name__ == "__main__":
    main()
