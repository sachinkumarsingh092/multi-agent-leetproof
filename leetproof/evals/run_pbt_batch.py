#!/usr/bin/env python3
"""
Batch PBT test runner for spec files.

Samples N spec files from a directory, fixes their headers for the current
project, runs spec_bug_finder on each, and prints a summary.

Usage:
    python -m utils.run_pbt_batch \
        --spec-dir llmgen-experiments/llmgen/TestSpecPBT/Verina \
        --output-file llmgen-experiments/llmgen/pbt_verify.lean \
        --build-dir llmgen-experiments \
        [--sample 30] [--seed 42]
"""

import argparse
import contextlib
import io
import os
import random
import re
import shutil
import sys
import time

from utils.spec_bug_finder import generate_and_check

# ─── Header replacement ────────────────────────────────────────────────────────

OLD_HEADER_IMPORTS = [
    "import CaseStudies.Velvet.Std",
    "import CaseStudies.TestingUtil",
    "import CaseStudies.Velvet.SpecDSL",
    "import CaseStudies.Velvet.Utils",
    "import CaseStudies.Velvet.UtilsLemmas",
]

NEW_HEADER = """\
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic\
"""


def fix_header(content: str) -> str:
    """Replace CaseStudies-style imports with the Extensions-style equivalents.

    Extra Mathlib imports that are not part of the boilerplate are preserved.
    """
    lines = content.splitlines()
    old_set = set(OLD_HEADER_IMPORTS)

    # Collect extra Mathlib imports that appear in the old header block
    # (before the first set_option / non-import line after the old block)
    extra_mathlib = []
    out_lines = []
    old_block_done = False

    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        if not old_block_done:
            if stripped in old_set:
                i += 1
                continue
            # Mathlib imports that are NOT Mathlib.Tactic get kept as extras
            if stripped.startswith("import Mathlib.") and stripped != "import Mathlib.Tactic":
                extra_mathlib.append(stripped)
                i += 1
                continue
            # "import Mathlib.Tactic" — absorbed into new header
            if stripped == "import Mathlib.Tactic":
                i += 1
                continue
            # First non-header line: emit new header + extras, then continue
            old_block_done = True
            out_lines.append(NEW_HEADER)
            for em in extra_mathlib:
                out_lines.append(em)
            out_lines.append("")  # blank line separator

        out_lines.append(line)
        i += 1

    if not old_block_done:
        # File was entirely header (shouldn't happen)
        out_lines.append(NEW_HEADER)

    return "\n".join(out_lines)


# ─── Batch runner ──────────────────────────────────────────────────────────────

OUTCOME_LABEL = {
    "bug":              "🐛 BUG  ",
    "no_bug":           "✅ OK   ",
    "synthesis_failed": "⚠️  SYN  ",
    "error":            "❌ ERR  ",
}


def _resolve_files(spec_dir: str, problems: list[str] | None,
                   sample: int, seed: int) -> list[tuple[str, str]]:
    """Return list of (problem_id, file_path) to test."""
    if problems:
        result = []
        for pid in problems:
            # Accept bare name (verina_advanced_8) or with .lean suffix
            pid = pid.removesuffix(".lean")
            path = os.path.join(spec_dir, f"{pid}.lean")
            if not os.path.exists(path):
                print(f"[WARN] {path} not found, skipping", file=sys.stderr)
            else:
                result.append((pid, path))
        return result

    # Sample mode
    all_files = sorted(f for f in os.listdir(spec_dir) if f.endswith(".lean"))
    rng = random.Random(seed)
    chosen = rng.sample(all_files, min(sample, len(all_files)))
    return [(f.removesuffix(".lean"), os.path.join(spec_dir, f)) for f in chosen]


class _TeeStream:
    """Write to both real stdout and a StringIO buffer simultaneously."""
    def __init__(self, buf: io.StringIO):
        self._buf = buf
        self._real = sys.__stdout__

    def write(self, s: str) -> int:
        if self._real:
            self._real.write(s)
            self._real.flush()
        return self._buf.write(s)

    def flush(self):
        if self._real:
            self._real.flush()
        self._buf.flush()


def run_batch(spec_dir: str, output_file: str, build_dir: str,
              problems: list[str] | None, sample: int, seed: int):
    targets = _resolve_files(spec_dir, problems, sample, seed)
    total = len(targets)

    print(f"{'─'*64}")
    print(f"  Running PBT on {total} problem(s)")
    print(f"  Output: {output_file}  |  Build: {build_dir}")
    print(f"{'─'*64}")

    results: dict[str, tuple[str, float, str | None]] = {}  # pid -> (outcome, elapsed, bug_case)

    for idx, (pid, src_path) in enumerate(targets, 1):
        print(f"\n{'━'*64}")
        print(f"  [{idx:02d}/{total}]  {pid}")
        print(f"{'━'*64}", flush=True)

        t0 = time.monotonic()
        buf = io.StringIO()
        tee = _TeeStream(buf)
        outcome = "error"
        try:
            with contextlib.redirect_stdout(tee):
                result_tuple = generate_and_check(src_path, output_file, build_dir)
                outcome = result_tuple[0]
        except Exception as e:
            msg = f"EXCEPTION: {e}\n"
            buf.write(msg)
            if sys.__stdout__:
                sys.__stdout__.write(msg)
        elapsed = time.monotonic() - t0

        bug_case: str | None = None
        if outcome == "bug":
            for line in buf.getvalue().splitlines():
                m = re.search(r"\[SPECIFICATION BUG FOUND\] on (\S+)", line)
                if m:
                    bug_case = m.group(1)
                    break
            # Preserve the theorem that triggered the bug next to the spec file
            bug_file = src_path.replace(".lean", ".bug.lean")
            try:
                shutil.copy2(output_file, bug_file)
                print(f"  Bug theorem saved to: {bug_file}", flush=True)
            except Exception as e:
                print(f"  [WARN] Could not save bug file: {e}", flush=True)

        label = OUTCOME_LABEL.get(outcome, f"?{outcome}?")
        print(f"\n  ──> {label}  {elapsed:.1f}s", flush=True)
        results[pid] = (outcome, elapsed, bug_case)

    # ── Summary table ─────────────────────────────────────────────────────────
    counts: dict[str, int] = {}
    total_elapsed = 0.0
    for outcome, elapsed, _ in results.values():
        counts[outcome] = counts.get(outcome, 0) + 1
        total_elapsed += elapsed

    print(f"\n{'═'*64}")
    print(f"  SUMMARY  ({total} problems, {total_elapsed:.0f}s total, avg {total_elapsed/total:.0f}s)")
    print(f"{'═'*64}")
    for pid, src_path in targets:
        outcome, elapsed, bug_case = results[pid]
        label = OUTCOME_LABEL.get(outcome, f"?{outcome}?")
        suffix = f"  (on {bug_case})" if bug_case else ""
        print(f"  {label}  {elapsed:6.1f}s  {pid}{suffix}")
    print(f"{'─'*64}")
    print(f"  🐛 BUG:              {counts.get('bug', 0)}")
    print(f"  ✅ OK (no bug):      {counts.get('no_bug', 0)}")
    print(f"  ⚠️  Synthesis failed: {counts.get('synthesis_failed', 0)}")
    print(f"  ❌ Error:            {counts.get('error', 0)}")
    if total:
        print(f"  Bug rate:     {counts.get('bug', 0)/total*100:.1f}%")
        print(f"  Conclusive:   {(counts.get('bug',0)+counts.get('no_bug',0))/total*100:.1f}%")


def main():
    parser = argparse.ArgumentParser(description="Batch PBT spec bug finder")
    parser.add_argument("--spec-dir", required=True,
                        help="Directory containing .lean spec files")
    parser.add_argument("--output-file", required=True,
                        help="Temporary lean output file for each test run")
    parser.add_argument("--build-dir", required=True,
                        help="Directory to run lake build from")

    group = parser.add_mutually_exclusive_group()
    group.add_argument("--problems", nargs="+", metavar="ID",
                       help="Specific problem IDs to test (e.g. verina_advanced_8)")
    group.add_argument("--sample", type=int, default=30,
                       help="Number of files to randomly sample (default: 30)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed for sampling (default: 42)")
    args = parser.parse_args()

    run_batch(args.spec_dir, args.output_file, args.build_dir,
              args.problems, args.sample, args.seed)


if __name__ == "__main__":
    main()
