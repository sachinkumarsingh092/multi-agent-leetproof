#!/usr/bin/env python3
"""Analyze and group Lean files by their numeric identifier."""

from __future__ import annotations

import json
import argparse
import re
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import LiteralString, Optional

from collections import Counter
from typing import Any

from agents.agent_state import PBTStatus
from tools.lean_build import lean_build_file_helper
from utils.lean.parser import LeanFile, parse_test_cases
from utils.velvet_helpers import get_velvet_method, get_pbt_counterexamples
from logging_config import get_logger

logger = get_logger(__name__)

ANALYZE_LEAN_BUILD_TIMEOUT_SECONDS = 600


class DafnySynthStatus:
    NA = "N/A"
    VERIFIES = "Verifies"
    FAILED = "Failed"


class LeanImplProofStatus:
    NA = "N/A"
    COMPLETED = "completed"
    PARTIAL = "partial"
    MISSING = "missing"
    POSSIBLE_ENV_ISSUE = "possible-env-issue"


def run_dafny_verify(file_path: str, timeout: int = 120) -> str:
    """Run Dafny verification and execution on a file.

    Uses `dafny run --target:py` to verify and execute the program.

    Args:
        file_path: Path to the .dfy file
        timeout: Timeout in seconds

    Returns:
        DafnySynthStatus value
    """
    try:
        result = subprocess.run(
            ["dafny", "run", "--target:py", file_path],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return DafnySynthStatus.VERIFIES if result.returncode == 0 else DafnySynthStatus.FAILED
    except subprocess.TimeoutExpired:
        return DafnySynthStatus.FAILED
    except FileNotFoundError:
        logger.warning("Dafny not found in PATH")
        return DafnySynthStatus.FAILED
    except Exception as e:
        logger.warning(f"Error running Dafny: {e}")
        return DafnySynthStatus.FAILED


def analyze_json_stats(data: dict[str, dict[str, Any]]) -> dict[str, dict[str, int]]:
    """Analyze JSON data and return value counts for each field."""
    fields: dict[str, list[str]] = {}
    for entry in data.values():
        for key, value in entry.items():
            if key not in fields:
                fields[key] = []
            fields[key].append(value)

    return {field: dict(Counter(values)) for field, values in fields.items()}


def print_analysis_stats(stats: dict[str, dict[str, int]], total: int) -> None:
    """Print formatted analysis statistics."""
    from rich.console import Console
    from rich.panel import Panel
    
    console = Console()
    console.print(Panel(f"[bold green]AGGREGATED STATISTICS (n={total})[/bold green]"))

    for field_name, value_counts in stats.items():
        console.print(f"\n[bold]{field_name}:[/bold]")
        for value, count in sorted(value_counts.items(), key=lambda x: -x[1]):
            pct = 100 * count / total
            console.print(f"  {value}: {count} ({pct:.1f}%)")


def analyze_json_file(json_path: Path) -> None:
    """Load and analyze a JSON file."""
    from rich.console import Console
    from rich.panel import Panel

    console = Console()

    if not json_path.exists():
        console.print(f"[bold red]Error:[/bold red] {json_path} does not exist")
        return

    with open(json_path) as f:
        data = json.load(f)

    # Categorize files by status
    lean_proof_completed = []
    lean_proof_partial = []
    lean_proof_missing = []
    dafny_verifies = []
    dafny_fails = []
    dafny_na = []

    for num, entry in data.items():
        # Lean proof status
        proof = entry.get("proof", "-")
        if proof == "completed":
            lean_proof_completed.append(num)
        elif proof == "partial":
            lean_proof_partial.append(num)
        else:
            lean_proof_missing.append(num)

        # Dafny status
        dafny = entry.get("dafny_synth", "N/A")
        if dafny == "Verifies":
            dafny_verifies.append(num)
        elif dafny == "Failed":
            dafny_fails.append(num)
        else:
            dafny_na.append(num)

    # Print detailed breakdown
    console.print(Panel("[bold cyan]DETAILED FILE STATUS[/bold cyan]"))

    console.print(f"\n[bold]Lean Proof Completed ({len(lean_proof_completed)}):[/bold]")
    if lean_proof_completed:
        console.print(f"  {', '.join(str(x) for x in sorted(lean_proof_completed))}")
    else:
        console.print("  (none)")

    console.print(f"\n[bold]Lean Proof Partial ({len(lean_proof_partial)}):[/bold]")
    if lean_proof_partial:
        console.print(f"  {', '.join(str(x) for x in sorted(lean_proof_partial))}")
    else:
        console.print("  (none)")

    console.print(f"\n[bold]Lean Proof Missing ({len(lean_proof_missing)}):[/bold]")
    if lean_proof_missing:
        console.print(f"  {', '.join(str(x) for x in sorted(lean_proof_missing))}")
    else:
        console.print("  (none)")

    console.print(f"\n[bold]Dafny Verifies ({len(dafny_verifies)}):[/bold]")
    if dafny_verifies:
        console.print(f"  {', '.join(str(x) for x in sorted(dafny_verifies))}")
    else:
        console.print("  (none)")

    console.print(f"\n[bold]Dafny Fails ({len(dafny_fails)}):[/bold]")
    if dafny_fails:
        console.print(f"  {', '.join(str(x) for x in sorted(dafny_fails))}")
    else:
        console.print("  (none)")

    # Cross-comparisons
    console.print()
    console.print(Panel("[bold cyan]CROSS-COMPARISONS[/bold cyan]"))

    # Both fully verified
    both_verified = set(lean_proof_completed) & set(dafny_verifies)
    console.print(f"\n[bold]Both Lean & Dafny Verified ({len(both_verified)}):[/bold]")
    if both_verified:
        console.print(f"  {', '.join(str(x) for x in sorted(both_verified))}")
    else:
        console.print("  (none)")

    # Dafny verifies but Lean proof not completed
    dafny_yes_lean_no = set(dafny_verifies) - set(lean_proof_completed)
    console.print(f"\n[bold]Dafny Verifies but Lean Proof Not Completed ({len(dafny_yes_lean_no)}):[/bold]")
    if dafny_yes_lean_no:
        console.print(f"  {', '.join(str(x) for x in sorted(dafny_yes_lean_no))}")
    else:
        console.print("  (none)")

    # Lean proof completed but Dafny fails
    lean_yes_dafny_no = set(lean_proof_completed) & set(dafny_fails)
    console.print(f"\n[bold]Lean Proof Completed but Dafny Fails ({len(lean_yes_dafny_no)}):[/bold]")
    if lean_yes_dafny_no:
        console.print(f"  {', '.join(str(x) for x in sorted(lean_yes_dafny_no))}")
    else:
        console.print("  (none)")

    # Lean proof completed but Dafny N/A
    lean_yes_dafny_na = set(lean_proof_completed) & set(dafny_na)
    console.print(f"\n[bold]Lean Proof Completed but Dafny N/A ({len(lean_yes_dafny_na)}):[/bold]")
    if lean_yes_dafny_na:
        console.print(f"  {', '.join(str(x) for x in sorted(lean_yes_dafny_na))}")
    else:
        console.print("  (none)")

    # Aggregate stats
    stats = analyze_json_stats(data)
    print_analysis_stats(stats, len(data))

@dataclass
class SpecAnalysis:
    typechecks: str  # TypecheckStatus value
    examples_cnt: int


@dataclass
class ExampleVerifyAnalysis:
    """Analysis result for spec_example_verify file."""

    precondition_cnt: int
    postcondition_cnt: int
    has_uniqueness: bool

    @property
    def total_cnt(self) -> int:
        return self.precondition_cnt + self.postcondition_cnt + (1 if self.has_uniqueness else 0)


class TypecheckStatus:
    PASSED = "passed"
    FAILED = "failed"
    TIMED_OUT = "timed_out"
    ERROR = "error"  # unexpected error during analysis


class ProofStatus:
    COMPLETED = "completed"  # no sorry in Proof section
    PARTIAL = "partial"      # has sorry in Proof section
    MISSING = "missing"      # no Proof section
    POSSIBLE_ENV_ISSUE = "possible-env-issue"  # build fails with no sorry/admit present


@dataclass
class ImplAnalysis:
    """Analysis result for impl file."""

    typechecks: str  # TypecheckStatus value
    has_assertions: bool
    pbt_status: PBTStatus
    pbt_counterexample_cnt: int
    proof_status: str
    goal_cnt: int
    has_while_loop: bool
    has_dummy_invariant: bool


@dataclass
class AnalysisResult:
    """Combined analysis result for a file group."""

    spec: Optional[SpecAnalysis] = None
    example_verify: Optional[ExampleVerifyAnalysis] = None
    impl: Optional[ImplAnalysis] = None
    dafny_synth: str = DafnySynthStatus.NA
    lean_impl_proof: str = LeanImplProofStatus.NA


def analyze_spec(path: Path) -> SpecAnalysis:
    """Analyze a spec file."""
    spec_file = LeanFile.from_path(path)

    try:
        build_res = lean_build_file_helper(
            str(path),
            timeout_seconds=ANALYZE_LEAN_BUILD_TIMEOUT_SECONDS,
        )
        typechecks = TypecheckStatus.PASSED if build_res.typechecks else TypecheckStatus.FAILED
    except TimeoutError:
        return SpecAnalysis(TypecheckStatus.TIMED_OUT, 0)

    if typechecks != TypecheckStatus.PASSED:
        return SpecAnalysis(typechecks, 0)

    test_cases_section = spec_file.get_section('TestCases')
    if not test_cases_section:
        return SpecAnalysis(typechecks, 0)

    file_content = path.read_text()
    method = get_velvet_method(file_content)
    test_cases = parse_test_cases(test_cases_section.content, method)
    return SpecAnalysis(typechecks, len(test_cases))




PRECONDITION_RE = re.compile(r'\btheorem\s+\w+_precondition\b')
POSTCONDITION_RE = re.compile(r'\btheorem\s+\w+_postcondition\b')
UNIQUENESS_RE = re.compile(r'\btheorem\s+uniqueness\b')


def analyze_example_verify(path: Path) -> ExampleVerifyAnalysis:
    """Analyze a spec_example_verify file."""
    content = path.read_text()

    precondition_cnt = len(PRECONDITION_RE.findall(content))
    postcondition_cnt = len(POSTCONDITION_RE.findall(content))
    has_uniqueness = bool(UNIQUENESS_RE.search(content))

    return ExampleVerifyAnalysis(precondition_cnt, postcondition_cnt, has_uniqueness)


GOAL_RE = re.compile(r'\btheorem\s+goal_\d+\b')
RUN_ELAB_UNCOMMENTED_RE = re.compile(r'^(?!.*--).*\brun_elab\b', re.MULTILINE)
RUN_ELAB_COMMENTED_RE = re.compile(r'--.*\brun_elab\b')
WHILE_LOOP_RE = re.compile(r'\bwhile\b')
PROVE_CORRECT_RE = re.compile(r'^\s*prove_correct\b', re.MULTILINE)
CORRECTNESS_GOAL_RE = re.compile(r'\btheorem\s+correctness_goal\b')
ADMIT_RE = re.compile(r'\badmit\b')
DUMMY_INVARIANT_RE = re.compile(r'invariant\s+(?:\"[^\"]*\"\s+)?(?:True\s*=\s*True|true\s*=\s*true)', re.IGNORECASE)


def has_sorry_or_admit(content: str) -> bool:
    return 'sorry' in content or bool(ADMIT_RE.search(content))


def find_aristotle_proof_path(base_path: Path) -> Optional[Path]:
    """Find a related Aristotle proof file beside a source file.

    Supports both flat files like `ImplAristotleProof.lean` and directory-based
    layouts like `LeanImplAristotleProof/LeanImplAristotleProof.lean`.
    """
    parent = base_path.parent
    stem = base_path.stem
    candidates: list[Path] = []

    candidates.extend(sorted(parent.glob(f"{stem}*AristotleProof.lean")))

    for proof_dir in sorted(parent.glob(f"{stem}*AristotleProof")):
        if not proof_dir.is_dir():
            continue
        exact = proof_dir / f"{proof_dir.name}.lean"
        if exact.exists():
            candidates.append(exact)
        candidates.extend(sorted(proof_dir.glob(f"{stem}*AristotleProof.lean")))

    seen: set[Path] = set()
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        return candidate

    return None


@contextmanager
def maybe_without_pbt(path: Path, skip_pbt: bool):
    """Yield a path to use for building. If skip_pbt, yield a temp file with Pbt section cleared."""
    if not skip_pbt:
        yield path
        return

    lean_file = LeanFile.from_path(path)
    if not lean_file.has_section('Pbt'):
        yield path
        return

    lean_file.clear_section('Pbt')
    content = lean_file.reconstruct()
    suffix = path.suffix
    with tempfile.NamedTemporaryFile(mode='w', suffix=suffix, delete=False, dir=path.parent) as tmp:
        tmp.write(content)
        tmp_path = Path(tmp.name)
    try:
        yield tmp_path
    finally:
        tmp_path.unlink(missing_ok=True)


def analyze_impl(path: Path, skip_pbt: bool = False) -> ImplAnalysis:
    """Analyze an impl file."""
    try:
        with maybe_without_pbt(path, skip_pbt) as build_path:
            build_res = lean_build_file_helper(
                str(build_path),
                timeout_seconds=ANALYZE_LEAN_BUILD_TIMEOUT_SECONDS,
            )
        typechecks = TypecheckStatus.PASSED if build_res.typechecks else TypecheckStatus.FAILED
    except TimeoutError:
        # Return minimal analysis result on timeout
        impl_file = LeanFile.from_path(path)
        content = path.read_text()
        method = get_velvet_method(content)
        method_body = method.body or ""
        return ImplAnalysis(
            typechecks=TypecheckStatus.TIMED_OUT,
            has_assertions=impl_file.has_section('Assertions'),
            pbt_status=PBTStatus.NOT_ATTEMPTED,
            pbt_counterexample_cnt=0,
            proof_status=ProofStatus.MISSING,
            goal_cnt=len(GOAL_RE.findall(content)),
            has_while_loop=bool(WHILE_LOOP_RE.search(method_body)),
            has_dummy_invariant=bool(DUMMY_INVARIANT_RE.search(method_body)),
        )

    impl_file = LeanFile.from_path(path)
    content = path.read_text()

    # Check Assertions section
    has_assertions = impl_file.has_section('Assertions')

    # Check Pbt section and counterexamples
    pbt_section = impl_file.get_section('Pbt')
    pbt_counterexample_cnt = 0
    if not pbt_section:
        pbt_status = PBTStatus.NOT_ATTEMPTED
    else:
        pbt_content = pbt_section.content
        if RUN_ELAB_UNCOMMENTED_RE.search(pbt_content):
            # PBT is active, check for counterexamples in build diagnostics
            counterexamples = get_pbt_counterexamples(build_res.diagnostics)
            pbt_counterexample_cnt = len(counterexamples)
            pbt_status = PBTStatus.ADDED_AND_PASSED
        elif RUN_ELAB_COMMENTED_RE.search(pbt_content):
            pbt_status = PBTStatus.ADDED_COMPILE_FAILED
        else:
            pbt_status = PBTStatus.NOT_ADDED

    # Check Proof section
    proof_section = impl_file.get_section('Proof')
    if not proof_section:
        proof_status = ProofStatus.MISSING
    else:
        proof_content = proof_section.content
        has_prove_correct = bool(PROVE_CORRECT_RE.search(proof_content))
        has_goal_theorems = bool(GOAL_RE.search(proof_content))
        has_proof_attempt = has_prove_correct or has_goal_theorems
        if not has_proof_attempt:
            proof_status = ProofStatus.MISSING
        elif has_sorry_or_admit(content):
            proof_status = ProofStatus.PARTIAL
            ari = check_aristotle_proof(path)
            if ari == "proven":
                proof_status = "partial/aristotle-proven"
            elif ari == "failure":
                proof_status = "partial/aristotle-failure"
        elif not typechecks:
            proof_status = ProofStatus.POSSIBLE_ENV_ISSUE
            ari = check_aristotle_proof(path)
            if ari == "proven":
                proof_status = "possible-env-issue/aristotle-proven"
            elif ari == "failure":
                proof_status = "possible-env-issue/aristotle-failure"
        else:
            proof_status = ProofStatus.COMPLETED

    # Count goals
    goal_cnt = len(GOAL_RE.findall(content))

    # Check for while loop in the method
    method = get_velvet_method(content)
    method_body = method.body or ""
    has_while_loop = bool(WHILE_LOOP_RE.search(method_body))
    has_dummy_invariant = bool(DUMMY_INVARIANT_RE.search(method_body))

    return ImplAnalysis(
        typechecks=typechecks,
        has_assertions=has_assertions,
        pbt_status=pbt_status,
        pbt_counterexample_cnt=pbt_counterexample_cnt,
        proof_status=proof_status,
        goal_cnt=goal_cnt,
        has_while_loop=has_while_loop,
        has_dummy_invariant=has_dummy_invariant,
    )


@dataclass
class FileGroup:
    """A group of related Lean files identified by a numeric ID."""

    key: str
    base_directory: Path = field(repr=False)
    spec_example_verify: Optional[str] = None
    impl: Optional[str] = None
    spec: Optional[str] = None
    dafny_impl: Optional[str] = None
    lean_impl: Optional[str] = None
    result: Optional[AnalysisResult] = None

    def get_full_path(self, file_type: str) -> Optional[Path]:
        """Get the full absolute path for a file type."""
        rel_path = getattr(self, file_type, None)
        if rel_path is None:
            return None
        return self.base_directory / rel_path

    @property
    def spec_example_verify_full(self) -> Optional[Path]:
        return self.get_full_path("spec_example_verify")

    @property
    def impl_full(self) -> Optional[Path]:
        return self.get_full_path("impl")

    @property
    def spec_full(self) -> Optional[Path]:
        return self.get_full_path("spec")

    @property
    def dafny_impl_full(self) -> Optional[Path]:
        return self.get_full_path("dafny_impl")

    @property
    def lean_impl_full(self) -> Optional[Path]:
        return self.get_full_path("lean_impl")


@dataclass
class PrefixSearchResult:
    """Result of searching a directory for Lean files by prefix."""

    prefix: str
    directory: Path
    groups: dict = field(default_factory=dict)

    def sorted_groups(self) -> list[FileGroup]:
        """Return groups sorted by their numeric ID."""
        return [self.groups[k] for k in sorted(self.groups.keys())]


_TRAILING_NUM = re.compile(r'(\d+)$')


def is_ignored_discovery_path(path: Path) -> bool:
    """Return whether a path should be skipped during problem discovery."""
    return ".lake" in path.parts


def find_and_group_files(directory: Path, prefix: str = "") -> PrefixSearchResult:
    """
    Auto-discover problem groups by finding spec files and deriving the rest.

    Finds *Spec.lean, *_spec.lean, and {Dir}/Spec.lean, extracts the trailing
    number, then uses derive_from_spec to locate related impl/verify/dafny files.
    """
    from utils.naming import derive_from_spec, OutputTarget

    result = PrefixSearchResult(prefix=prefix, directory=directory)

    # Collect all spec files (PascalCase flat, snake_case flat, directory-based)
    path_prefix = Path(directory) 
    if prefix:
        path_prefix = path_prefix / Path(prefix)
    spec_paths = [
        p
        for p in list(directory.rglob("*Spec.lean")) + list(directory.rglob("*_spec.lean"))
        if str(p).startswith(str(path_prefix)) and not is_ignored_discovery_path(p)
    ]
    # print(spec_paths)
    for spec_path in spec_paths:
        name = spec_path.name

        # Extract stem (the part before the spec suffix that contains the number)
        if name == "Spec.lean":
            stem = spec_path.parent.name       # directory-based
        elif name.endswith("Spec.lean"):
            stem = name[:-len("Spec.lean")]    # flat PascalCase
        elif name.endswith("_spec.lean"):
            stem = name[:-len("_spec.lean")]   # flat snake_case
        else:
            continue


        if stem not in result.groups:
            result.groups[stem] = FileGroup(key=stem, base_directory=directory)
        g = result.groups[stem]

        g.spec = str(spec_path.relative_to(directory))

        # Derive related files
        spec_str = str(spec_path)
        for target, attr in [
            (OutputTarget.IMPL, "impl"),
            (OutputTarget.EXAMPLE_VERIFY, "spec_example_verify"),
            (OutputTarget.DAFNY_IMPL, "dafny_impl"),
            (OutputTarget.LEAN_IMPL, "lean_impl"),
        ]:
            derived = Path(derive_from_spec(spec_str, target))
            if derived.exists():
                setattr(g, attr, str(derived.relative_to(directory)))

    return result


def main():
    parser = argparse.ArgumentParser(description="Analyze and group Lean files by numeric identifier")
    parser.add_argument("directory", type=Path, nargs="?", help="Directory to search in")
    parser.add_argument("prefix", type=str, nargs="?", help="File name prefix to search for")
    parser.add_argument("-n", "--limit", type=int, default=None, help="Only analyze first N file groups")
    parser.add_argument("-j", "--jobs", type=int, default=4, help="Number of parallel jobs (default: 4)")
    parser.add_argument("-o", "--outputfile", type=Path, default=None, help="Output json file name")
    parser.add_argument("-a", "--analyze", type=Path, default=None, help="Analyze existing JSON file")
    parser.add_argument("--skip-pbt", action="store_true", default=False, help="Ignore section Pbt when building Lean impl files")
    args = parser.parse_args()

    # If --analyze is provided, just analyze the JSON file
    if args.analyze:
        analyze_json_file(args.analyze)
        return 0

    # Otherwise, require directory and prefix
    if not args.directory :
        parser.error("directory and prefix are required unless using --analyze")

    if not args.directory.is_dir():
        print(f"Error: {args.directory} is not a valid directory")
        return 1

    result = find_and_group_files(args.directory, args.prefix)
    groups_to_analyze = result.sorted_groups()[:args.limit]

    print(f"Analyzing {len(groups_to_analyze)} file groups for prefix '{result.prefix}' with {args.jobs} workers...\n")

    def analyze_with_id(group: FileGroup) -> tuple[str, AnalysisResult]:
        return group.key, analyze_group(group, skip_pbt=args.skip_pbt)

    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {executor.submit(analyze_with_id, g): g for g in groups_to_analyze}
        for future in as_completed(futures):
            group = futures[future]
            try:
                key, analysis_result = future.result()
                group.result = analysis_result
                print(f"Completed analysis for id {key}")
            except Exception as e:
                print(f"Error analyzing id {group.key}: {e}")

    print_results_table(groups_to_analyze, args.outputfile)

    return 0


def check_aristotle_proof(base_path: Path) -> Optional[str]:
    """Check if a related Aristotle proof exists and has no sorry/admit markers."""
    aristotle_path = find_aristotle_proof_path(base_path)
    if aristotle_path is None:
        return None

    content = aristotle_path.read_text()
    if has_sorry_or_admit(content):
        return "failure"
    return "proven"


def analyze_lean_impl(path: Path) -> str:
    """Analyze a LeanImpl.lean file and return a LeanImplProofStatus value."""
    try:
        build_res = lean_build_file_helper(
            str(path),
            timeout_seconds=ANALYZE_LEAN_BUILD_TIMEOUT_SECONDS,
        )
        typechecks = build_res.typechecks
    except TimeoutError:
        typechecks = False

    lean_file = LeanFile.from_path(path)
    proof_section = lean_file.get_section('Proof')

    if not proof_section or not CORRECTNESS_GOAL_RE.search(proof_section.content):
        return LeanImplProofStatus.MISSING

    # Check the whole file so helper lemmas/imported proof scaffolding are counted too
    if has_sorry_or_admit(content := path.read_text()):
        ari = check_aristotle_proof(path)
        if ari == "proven":
            return "partial/aristotle-proven"
        elif ari == "failure":
            return "partial/aristotle-failure"
        return LeanImplProofStatus.PARTIAL
    if not typechecks:
        ari = check_aristotle_proof(path)
        if ari == "proven":
            return "possible-env-issue/aristotle-proven"
        elif ari == "failure":
            return "possible-env-issue/aristotle-failure"
        return LeanImplProofStatus.POSSIBLE_ENV_ISSUE
    return LeanImplProofStatus.COMPLETED


def analyze_group(group: FileGroup, skip_pbt: bool = False) -> AnalysisResult:
    """Analyze all files in a group."""
    print(f"Analyzing {group.spec} and {group.impl}")
    result = AnalysisResult()

    if group.spec_full and group.spec_full.exists():
        try:
            result.spec = analyze_spec(group.spec_full)
        except Exception as e:
            print(f"  Error analyzing spec {group.spec}: {e}")

    if group.spec_example_verify_full and group.spec_example_verify_full.exists():
        try:
            result.example_verify = analyze_example_verify(group.spec_example_verify_full)
        except Exception as e:
            print(f"  Error analyzing example_verify {group.spec_example_verify}: {e}")

    if group.impl_full and group.impl_full.exists():
        try:
            result.impl = analyze_impl(group.impl_full, skip_pbt=skip_pbt)
        except Exception as e:
            print(f"  Error analyzing impl {group.impl}: {e}")

    if group.dafny_impl_full and group.dafny_impl_full.exists():
        try:
            result.dafny_synth = run_dafny_verify(str(group.dafny_impl_full))
        except Exception as e:
            print(f"  Error analyzing dafny_impl {group.dafny_impl}: {e}")
            result.dafny_synth = DafnySynthStatus.FAILED

    if group.lean_impl_full and group.lean_impl_full.exists():
        try:
            result.lean_impl_proof = analyze_lean_impl(group.lean_impl_full)
        except Exception as e:
            print(f"  Error analyzing lean_impl {group.lean_impl}: {e}")
            result.lean_impl_proof = LeanImplProofStatus.MISSING

    return result


def print_results_table(groups: list[FileGroup], output_file: str) -> None:
    """Print analysis results in tabular format."""
    from rich.console import Console
    from rich.table import Table

    console = Console()
    table = Table(show_header=True, header_style="bold magenta", title="Detailed File Status")

    table.add_column("Key", justify="left")
    table.add_column("Spec TC", justify="center")
    table.add_column("Typechecks", justify="center")
    table.add_column("DummyInv", justify="center")
    table.add_column("Proof", justify="left")
    table.add_column("LeanImpl", justify="left")
    table.add_column("Dafny", justify="left")
    table.add_column("Verdict", justify="left")

    stats = {}
    for group in groups:
        res = group.result
        if not res:
            table.add_row(
                group.key, "N/A", "N/A", "N/A", "N/A", "N/A", "N/A", "N/A"
            )
            continue

        # Spec columns
        if res.spec:
            spec_tc = {"passed": "Y", "failed": "N", "timed_out": "T", "error": "E"}.get(res.spec.typechecks, "?")
        else:
            spec_tc = "-"
            
        # Impl columns
        if res.impl:
            impl_tc = {"passed": "Y", "failed": "N", "timed_out": "T", "error": "E"}.get(res.impl.typechecks, "?")
            dummy_inv = "Y" if res.impl.has_dummy_invariant else "N"
        else:
            impl_tc = "-"
            dummy_inv = "-"
            
        proof = res.impl.proof_status if res.impl else "-"

        # Dafny column
        dafny = res.dafny_synth

        # LeanImpl column
        lean_impl = res.lean_impl_proof

        # Calculate Velvet Synth Verdict
        if not res.impl:
            verdict = "spec-fail"
        elif res.impl.has_dummy_invariant:
            verdict = "prog-gen-fail"
        elif res.impl.proof_status == "missing":
            verdict = "inv-gen-fail"
        elif res.impl.proof_status.startswith("partial") or res.impl.proof_status.startswith("possible-env-issue"):
            if "aristotle-proven" in res.impl.proof_status:
                verdict = "proof-fail (ari-verified)"
            elif res.impl.proof_status.startswith("possible-env-issue"):
                verdict = "proof-fail (possible-env-issue)"
            else:
                verdict = "proof-fail"
        elif res.impl.proof_status == "completed":
            verdict = "e2e-verified"
        else:
            verdict = "unknown"

        # Store full status strings for JSON, use display abbreviations for table
        spec_tc_full = res.spec.typechecks if res.spec else "-"
        impl_tc_full = res.impl.typechecks if res.impl else "-"
        dummy_inv_full = res.impl.has_dummy_invariant if res.impl else False
        
        stats[group.key] = {
            "spec_tc": spec_tc_full, 
            "typechecks": impl_tc_full, 
            "dummy_invariant": dummy_inv_full, 
            "proof": proof, 
            "dafny_synth": dafny, 
            "lean_impl_proof": lean_impl,
            "velvet_synth_verdict": verdict
        }
        
        table.add_row(
            group.key, spec_tc, impl_tc, dummy_inv, proof, lean_impl, dafny, verdict
        )

    console.print(table)
    console.print("Legend: Y=passed, N=failed, T=timed_out, E=error, -=missing")

    if output_file:
        Path(output_file).write_text(json.dumps(stats, indent=2))

    # Print aggregated statistics
    if stats:
        agg_stats = analyze_json_stats({str(k): v for k, v in stats.items()})
        print_analysis_stats(agg_stats, len(stats))



if __name__ == "__main__":
    exit(main())
