from collections import Counter
from typing import List

from scripts.effectiveness_analysis_types import (
    SpecGenEffectivenessReport,
    ProgrammerEffectivenessReport,
    InferrerEffectivenessReport,
    LeanSynthEffectivenessReport,
)

def visualize_specgen_session(report: SpecGenEffectivenessReport):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    console.print(f"\n[bold cyan]=== SpecGen Effectiveness Report for Session: {report.session} ===[/bold cyan]")
    console.print(f"[bold]Spec Build Passed:[/bold] {report.builds.passed}/{report.builds.total}")
    
    console.print("\n[bold]Coach Verdict Counts:[/bold]")
    if not report.coach_verdict_counts:
        console.print("  None")
    for verdict, count in report.coach_verdict_counts.items():
        console.print(f"  {verdict}: {count}")

    console.print("\n[bold]Combination of Build, Coach Verdict, and PBT Result:[/bold]")
    if not report.attempt_combinations:
        console.print("  None")
    else:
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Build")
        table.add_column("Coach Verdict")
        table.add_column("PBT Result")
        table.add_column("Count", justify="right")
        
        for comb in report.attempt_combinations:
            table.add_row(str(comb.build), str(comb.coach), str(comb.pbt), str(comb.count))
        console.print(table)

    console.print(f"\n[bold]Final Outcome:[/bold] {report.final_outcome}\n")


def visualize_specgen_aggregate(reports: List[SpecGenEffectivenessReport]):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    total_sessions = len(reports)
    total_builds = sum(r.builds.total for r in reports)
    total_passed = sum(r.builds.passed for r in reports)
    
    overall_verdicts = Counter()
    overall_combinations = Counter()
    outcome_counts = Counter()
    
    for r in reports:
        for verdict, count in r.coach_verdict_counts.items():
            overall_verdicts[verdict] += count
            
        for comb in r.attempt_combinations:
            overall_combinations[(comb.build, comb.coach, comb.pbt)] += comb.count
            
        outcome_counts[r.final_outcome] += 1
        
    console.print(Panel(f"[bold green]SpecGen Aggregate Report ({total_sessions} Sessions)[/bold green]"))
    console.print(f"[bold]Overall Spec Build Passed:[/bold] {total_passed}/{total_builds}")
    
    console.print("\n[bold]Final Outcomes:[/bold]")
    for outcome, count in outcome_counts.most_common():
        console.print(f"  {outcome}: {count} ({(count/total_sessions)*100:.1f}%)")

    console.print("\n[bold]Aggregate Coach Verdict Counts:[/bold]")
    for verdict, count in overall_verdicts.most_common():
        console.print(f"  {verdict}: {count}")

    console.print("\n[bold]Aggregate Combination of Build, Coach Verdict, and PBT Result:[/bold]")
    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("Build")
    table.add_column("Coach Verdict")
    table.add_column("PBT Result")
    table.add_column("Total Count", justify="right")
    
    sorted_combs = sorted(overall_combinations.items(), key=lambda x: (str(x[0][0]) != "True", str(x[0][1]), str(x[0][2])))
    for (b, c, p), count in sorted_combs:
        table.add_row(str(b), str(c), str(p), str(count))
    console.print(table)
    console.print()
def visualize_programmer_session(report: ProgrammerEffectivenessReport):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    console.print(f"\n[bold cyan]=== Programmer Effectiveness Report for Session: {report.session} ===[/bold cyan]")
    
    console.print("[bold]Build Statistics:[/bold]")
    console.print(f"  Total Attempts: {report.build_stats.total_attempts}")
    console.print(f"  Builds Passed: {report.build_stats.build_passed}")
    console.print(f"  Builds Failed: {report.build_stats.build_failed}")
    console.print(f"  Assertion Failures: {report.build_stats.assertion_failures}")
    console.print(f"  PBT Failures: {report.build_stats.pbt_failures}")

    console.print("\n[bold]Judge Statistics:[/bold]")
    console.print(f"  Triggered: {report.judge_stats.triggered}")
    console.print(f"  Passed: {report.judge_stats.passed}")
    console.print(f"  Failed: {report.judge_stats.failed}")

    console.print("\n[bold]Attempt Details:[/bold]")
    if not report.attempts:
        console.print("  None")
    else:
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Attempt")
        table.add_column("Build Passed")
        table.add_column("Assert Failure")
        table.add_column("PBT Failure")
        table.add_column("Judge Verdict")
        table.add_column("Outcome")
        
        for att in report.attempts:
            table.add_row(
                str(att.attempt_no),
                str(att.build_passed),
                str(att.assertion_failure),
                str(att.pbt_failure),
                str(att.judge_verdict),
                str(att.outcome),
            )
        console.print(table)

    console.print(f"\n[bold]Final Outcome:[/bold] {report.final_outcome}\n")


def visualize_programmer_aggregate(reports: List[ProgrammerEffectivenessReport]):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    total_sessions = len(reports)
    total_attempts = sum(r.build_stats.total_attempts for r in reports)
    total_passed = sum(r.build_stats.build_passed for r in reports)
    total_failed = sum(r.build_stats.build_failed for r in reports)
    total_assert_fails = sum(r.build_stats.assertion_failures for r in reports)
    total_pbt_fails = sum(r.build_stats.pbt_failures for r in reports)

    judge_triggered = sum(r.judge_stats.triggered for r in reports)
    judge_passed = sum(r.judge_stats.passed for r in reports)
    judge_failed = sum(r.judge_stats.failed for r in reports)

    outcome_counts = Counter()
    overall_combinations = Counter()
    
    for r in reports:
        outcome_counts[r.final_outcome] += 1
        for att in r.attempts:
            overall_combinations[(att.build_passed, att.assertion_failure, att.pbt_failure, att.judge_verdict)] += 1
        
    console.print(Panel(f"[bold green]Programmer Aggregate Report ({total_sessions} Sessions)[/bold green]"))
    
    console.print("[bold]Aggregate Build Statistics:[/bold]")
    console.print(f"  Total Attempts: {total_attempts}")
    console.print(f"  Builds Passed: {total_passed}")
    console.print(f"  Builds Failed: {total_failed}")
    console.print(f"  Assertion Failures: {total_assert_fails}")
    console.print(f"  PBT Failures: {total_pbt_fails}")

    console.print("\n[bold]Aggregate Judge Statistics:[/bold]")
    console.print(f"  Triggered: {judge_triggered}")
    console.print(f"  Passed: {judge_passed}")
    console.print(f"  Failed: {judge_failed}")

    console.print("\n[bold]Final Outcomes:[/bold]")
    for outcome, count in outcome_counts.most_common():
        console.print(f"  {outcome}: {count} ({(count/total_sessions)*100:.1f}%)")

    console.print("\n[bold]Aggregate Attempt Combinations:[/bold]")
    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("Build Passed")
    table.add_column("Assert Failure")
    table.add_column("PBT Failure")
    table.add_column("Judge Verdict")
    table.add_column("Total Count", justify="right")
    
    sorted_combs = sorted(overall_combinations.items(), key=lambda x: (
        not x[0][0],  # Build passed True first
        not x[0][1],  # Assert failure True first
        not x[0][2],  # PBT failure True first
        str(x[0][3])  # Judge Verdict
    ))
    
    for (b, a, p, j), count in sorted_combs:
        table.add_row(str(b), str(a), str(p), str(j), str(count))
        
    console.print(table)
    console.print()


def visualize_lean_synth_session(report: LeanSynthEffectivenessReport):
    from rich.console import Console
    from rich.table import Table

    console = Console()

    console.print(f"\n[bold cyan]=== Lean Synth Effectiveness Report for Session: {report.session} ===[/bold cyan]")

    console.print("[bold]Build Statistics:[/bold]")
    console.print(f"  Total Attempts: {report.build_stats.total_attempts}")
    console.print(f"  Validation Failures: {report.build_stats.validation_failures}")
    console.print(f"  Builds Passed: {report.build_stats.build_passed}")
    console.print(f"  Builds Failed: {report.build_stats.build_failed}")
    console.print(f"  PBT Failures: {report.build_stats.pbt_failures}")

    console.print("\n[bold]Judge Statistics:[/bold]")
    console.print(f"  Triggered: {report.judge_stats.triggered}")
    console.print(f"  Passed: {report.judge_stats.passed}")
    console.print(f"  Failed: {report.judge_stats.failed}")

    console.print("\n[bold]Proof Statistics:[/bold]")
    console.print(f"  Triggered: {report.proof_stats.triggered}")
    console.print(f"  Proven: {report.proof_stats.proven}")
    console.print(f"  Partial: {report.proof_stats.partial}")
    console.print(f"  Failed: {report.proof_stats.failed}")
    console.print(f"  Preparation Failed: {report.proof_stats.preparation_failed}")
    console.print(f"  Final Build Failed: {report.proof_stats.final_build_failed}")

    console.print("\n[bold]Attempt Details:[/bold]")
    if not report.attempts:
        console.print("  None")
    else:
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Attempt")
        table.add_column("Val Pass")
        table.add_column("Build Pass")
        table.add_column("PBT Fail")
        table.add_column("Judge")
        table.add_column("Proof")
        table.add_column("Sorry")
        table.add_column("Final Build")
        table.add_column("Outcome")

        for att in report.attempts:
            table.add_row(
                str(att.attempt_no),
                str(att.validation_passed),
                str(att.build_passed),
                str(att.pbt_failure),
                str(att.judge_verdict),
                str(att.proof_status),
                str(att.has_sorry),
                str(att.final_build_passed),
                str(att.outcome),
            )
        console.print(table)

    console.print(f"\n[bold]Final Outcome:[/bold] {report.final_outcome}\n")


def visualize_lean_synth_aggregate(reports: List[LeanSynthEffectivenessReport]):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel

    console = Console()

    total_sessions = len(reports)
    total_attempts = sum(r.build_stats.total_attempts for r in reports)
    total_validation_failures = sum(r.build_stats.validation_failures for r in reports)
    total_build_passed = sum(r.build_stats.build_passed for r in reports)
    total_build_failed = sum(r.build_stats.build_failed for r in reports)
    total_pbt_failures = sum(r.build_stats.pbt_failures for r in reports)
    judge_triggered = sum(r.judge_stats.triggered for r in reports)
    judge_passed = sum(r.judge_stats.passed for r in reports)
    judge_failed = sum(r.judge_stats.failed for r in reports)
    proof_triggered = sum(r.proof_stats.triggered for r in reports)
    proof_proven = sum(r.proof_stats.proven for r in reports)
    proof_partial = sum(r.proof_stats.partial for r in reports)
    proof_failed = sum(r.proof_stats.failed for r in reports)
    proof_preparation_failed = sum(r.proof_stats.preparation_failed for r in reports)
    final_build_failed = sum(r.proof_stats.final_build_failed for r in reports)

    outcome_counts = Counter()
    overall_combinations = Counter()
    for r in reports:
        outcome_counts[r.final_outcome] += 1
        for att in r.attempts:
            overall_combinations[
                (
                    att.validation_passed,
                    att.build_passed,
                    att.pbt_failure,
                    att.judge_verdict,
                    att.proof_status,
                    att.has_sorry,
                    att.final_build_passed,
                )
            ] += 1

    console.print(Panel(f"[bold green]Lean Synth Aggregate Report ({total_sessions} Sessions)[/bold green]"))
    console.print("[bold]Aggregate Build Statistics:[/bold]")
    console.print(f"  Total Attempts: {total_attempts}")
    console.print(f"  Validation Failures: {total_validation_failures}")
    console.print(f"  Builds Passed: {total_build_passed}")
    console.print(f"  Builds Failed: {total_build_failed}")
    console.print(f"  PBT Failures: {total_pbt_failures}")

    console.print("\n[bold]Aggregate Judge Statistics:[/bold]")
    console.print(f"  Triggered: {judge_triggered}")
    console.print(f"  Passed: {judge_passed}")
    console.print(f"  Failed: {judge_failed}")

    console.print("\n[bold]Aggregate Proof Statistics:[/bold]")
    console.print(f"  Triggered: {proof_triggered}")
    console.print(f"  Proven: {proof_proven}")
    console.print(f"  Partial: {proof_partial}")
    console.print(f"  Failed: {proof_failed}")
    console.print(f"  Preparation Failed: {proof_preparation_failed}")
    console.print(f"  Final Build Failed: {final_build_failed}")

    console.print("\n[bold]Final Outcomes:[/bold]")
    for outcome, count in outcome_counts.most_common():
        console.print(f"  {outcome}: {count} ({(count/total_sessions)*100:.1f}%)")

    console.print("\n[bold]Aggregate Attempt Combinations:[/bold]")
    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("Val Pass")
    table.add_column("Build Pass")
    table.add_column("PBT Fail")
    table.add_column("Judge")
    table.add_column("Proof")
    table.add_column("Sorry")
    table.add_column("Final Build")
    table.add_column("Total Count", justify="right")

    for (v, b, p, j, pr, s, fb), count in sorted(overall_combinations.items(), key=lambda x: str(x[0])):
        table.add_row(str(v), str(b), str(p), str(j), str(pr), str(s), str(fb), str(count))
    console.print(table)
    console.print()


def visualize_inferrer_session(report: InferrerEffectivenessReport):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    console.print(f"\n[bold cyan]=== Inferrer Effectiveness Report for Session: {report.session} ===[/bold cyan]")
    
    console.print("[bold]Build Statistics:[/bold]")
    console.print(f"  Total Attempts: {report.build_stats.total_attempts}")
    console.print(f"  Validation Failed: {report.build_stats.validation_failed}")
    console.print(f"  Builds Passed: {report.build_stats.build_passed}")
    console.print(f"  Builds Failed: {report.build_stats.build_failed}")
    console.print(f"  PBT Failures: {report.build_stats.pbt_failures}")

    console.print("\n[bold]Correctness Check Statistics:[/bold]")
    console.print(f"  Triggered: {report.correctness_stats.triggered}")
    console.print(f"  OK: {report.correctness_stats.ok}")
    console.print(f"  Issues Found: {report.correctness_stats.issues}")
    console.print(f"  Inconclusive: {report.correctness_stats.inconclusive}")
    console.print(f"  Counterexamples Found: {report.correctness_stats.counterexamples_found}")

    console.print("\n[bold]Attempt Details:[/bold]")
    if not report.attempts:
        console.print("  None")
    else:
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Attempt")
        table.add_column("Val Pass")
        table.add_column("Build Pass")
        table.add_column("PBT Fail")
        table.add_column("CE Found")
        table.add_column("Verdict")
        table.add_column("Outcome")
        
        for att in report.attempts:
            table.add_row(
                str(att.attempt_no),
                str(att.validation_passed),
                str(att.build_passed),
                str(att.pbt_failure),
                str(att.counterexample_found),
                str(att.correctness_verdict),
                str(att.outcome),
            )
        console.print(table)

    console.print(f"\n[bold]Final Outcome:[/bold] {report.final_outcome}\n")


def visualize_inferrer_aggregate(reports: List[InferrerEffectivenessReport]):
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    total_sessions = len(reports)
    total_attempts = sum(r.build_stats.total_attempts for r in reports)
    total_val_failed = sum(r.build_stats.validation_failed for r in reports)
    total_passed = sum(r.build_stats.build_passed for r in reports)
    total_failed = sum(r.build_stats.build_failed for r in reports)
    total_pbt_fails = sum(r.build_stats.pbt_failures for r in reports)

    corr_triggered = sum(r.correctness_stats.triggered for r in reports)
    corr_ok = sum(r.correctness_stats.ok for r in reports)
    corr_issues = sum(r.correctness_stats.issues for r in reports)
    corr_inconclusive = sum(r.correctness_stats.inconclusive for r in reports)
    corr_ce = sum(r.correctness_stats.counterexamples_found for r in reports)

    outcome_counts = Counter()
    overall_combinations = Counter()
    
    for r in reports:
        outcome_counts[r.final_outcome] += 1
        for att in r.attempts:
            overall_combinations[(att.validation_passed, att.build_passed, att.pbt_failure, att.counterexample_found, att.correctness_verdict)] += 1
        
    console.print(Panel(f"[bold green]Inferrer Aggregate Report ({total_sessions} Sessions)[/bold green]"))
    
    console.print("[bold]Aggregate Build Statistics:[/bold]")
    console.print(f"  Total Attempts: {total_attempts}")
    console.print(f"  Validation Failed: {total_val_failed}")
    console.print(f"  Builds Passed: {total_passed}")
    console.print(f"  Builds Failed: {total_failed}")
    console.print(f"  PBT Failures: {total_pbt_fails}")

    console.print("\n[bold]Aggregate Correctness Check Statistics:[/bold]")
    console.print(f"  Triggered: {corr_triggered}")
    console.print(f"  OK: {corr_ok}")
    console.print(f"  Issues Found: {corr_issues}")
    console.print(f"  Inconclusive: {corr_inconclusive}")
    console.print(f"  Counterexamples Found: {corr_ce}")

    console.print("\n[bold]Final Outcomes:[/bold]")
    for outcome, count in outcome_counts.most_common():
        console.print(f"  {outcome}: {count} ({(count/total_sessions)*100:.1f}%)")

    console.print("\n[bold]Aggregate Attempt Combinations:[/bold]")
    table = Table(show_header=True, header_style="bold magenta")
    table.add_column("Val Pass")
    table.add_column("Build Pass")
    table.add_column("PBT Fail")
    table.add_column("CE Found")
    table.add_column("Verdict")
    table.add_column("Total Count", justify="right")
    
    sorted_combs = sorted(overall_combinations.items(), key=lambda x: (
        not x[0][0],  # Val Pass True first
        not x[0][1],  # Build Pass True first
        not x[0][2],  # PBT Failure True first
        not x[0][3],  # CE Found True first
        str(x[0][4])  # Verdict
    ))
    
    for (v, b, p, c, j), count in sorted_combs:
        table.add_row(str(v), str(b), str(p), str(c), str(j), str(count))
        
    console.print(table)
    console.print()
