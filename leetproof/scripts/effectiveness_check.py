from collections import Counter
from dataclasses import dataclass
from agents.agent_state import JudgeVerdict
from utils.analytics.velvet_programmer import (
    query_attempt_meta as programmer_query_attempt_meta,
    query_typecheck_summaries as programmer_query_typecheck_summaries,
    query_judge_results as programmer_query_judge_results
)
from utils.analytics.velvet_invariant_inferrer import (
    query_attempt_meta as inferrer_query_attempt_meta,
    query_typecheck_summaries as inferrer_query_typecheck_summaries,
    query_correctness_summaries as inferrer_query_correctness_summaries
)
from utils.analytics.spec_generation import query_attempt_meta as specgen_query_attempt_meta, query_coach_reviews, query_pbt_summaries, query_typecheck_summaries
from utils.analytics.lean_synth_and_verify import (
    query_attempt_meta as lean_synth_query_attempt_meta,
    query_typecheck_summaries as lean_synth_query_typecheck_summaries,
    query_judge_results as lean_synth_query_judge_results,
    query_proof_summaries as lean_synth_query_proof_summaries,
    ProofStatus as LeanSynthProofStatus,
)
from scripts.effectiveness_analysis_types import (
    SpecGenBuildStats,
    SpecGenAttemptCombinationCount,
    SpecGenEffectivenessReport,
    ProgrammerAttempt,
    ProgrammerBuildStats,
    ProgrammerJudgeStats,
    ProgrammerEffectivenessReport,
    InferrerAttempt,
    InferrerBuildStats,
    InferrerCorrectnessStats,
    InferrerEffectivenessReport,
    LeanSynthAttempt,
    LeanSynthBuildStats,
    LeanSynthJudgeStats,
    LeanSynthProofStats,
    LeanSynthEffectivenessReport,
)

"""

The idea is to evaluate the effectiveness of our agents.

# SpecGen Effectiveness

- Report how many times the spec build passed (m/n)
- Report the count of each kind of feedback(CoachVerdict) from spec coach
- Report the combination of results from coach(the verdict) and the pbt summary(status of pbt).
- Report the final thing as well(this is based on the last attempt from attempt meta query I think).

# Programmer Effectiveness

- Report how many times the build failed (with the distribution of how, i think assertion failures, typecheck error, pbt stuff would be there)
- Report how many times the correctness check got triggered and how many times it failed (out of all the times).

# Inferred Effectiveness

TODO

"""


def evaluate_specgen_effectivess(session: str) -> SpecGenEffectivenessReport:
    attempts = specgen_query_attempt_meta(session)
    pbt_summaries = query_pbt_summaries(session)
    typecheck_summaries = query_typecheck_summaries(session)
    coach_summaries = query_coach_reviews(session)
    
    # 1. Report how many times the spec build passed (m/n)
    total_builds = len(typecheck_summaries)
    builds_passed = sum(1 for t in typecheck_summaries if t.payload.build_passed)
    build_stats = SpecGenBuildStats(passed=builds_passed, total=total_builds)

    # 2. Report the count of each kind of feedback(CoachVerdict) from spec coach
    verdict_counts = dict(Counter(c.payload.verdict.value for c in coach_summaries))

    # 3. Report the combination of results from build, coach, and pbt summary.
    build_by_attempt = {t.attempt_no: t.payload.build_passed for t in typecheck_summaries}
    coach_by_attempt = {c.attempt_no: c.payload.verdict.value for c in coach_summaries}
    pbt_by_attempt = {p.attempt_no: (p.payload.result.value if p.payload.result else "None") for p in pbt_summaries}
    
    all_attempts = sorted(set(build_by_attempt.keys()) | set(coach_by_attempt.keys()) | set(pbt_by_attempt.keys()))
    
    combination_counts = Counter()
    for att in all_attempts:
        build_val = build_by_attempt.get(att, "N/A")
        coach_val = coach_by_attempt.get(att, "N/A")
        pbt_val = pbt_by_attempt.get(att, "N/A")
        combination_counts[(build_val, coach_val, pbt_val)] += 1

    attempt_combinations = [
        SpecGenAttemptCombinationCount(
            build=b,
            coach=c,
            pbt=p,
            count=count
        )
        for (b, c, p), count in combination_counts.items()
    ]
    
    # Sort combinations by build (True first), then coach verdict, then PBT result
    attempt_combinations.sort(key=lambda x: (str(x.build) != "True", str(x.coach), str(x.pbt)))

    # 4. Report the final thing as well
    if attempts:
        last_attempt = max(attempts, key=lambda a: a.attempt_no)
        final_outcome = last_attempt.payload.final_outcome.value
    else:
        final_outcome = "N/A (No attempts found)"

    return SpecGenEffectivenessReport(
        session=session,
        builds=build_stats,
        coach_verdict_counts=verdict_counts,
        attempt_combinations=attempt_combinations,
        final_outcome=final_outcome,
    )


def evaluate_inferrer_effectiveness(session: str) -> InferrerEffectivenessReport:
    attempts = inferrer_query_attempt_meta(session)
    typecheck_summaries = inferrer_query_typecheck_summaries(session)
    correctness_summaries = inferrer_query_correctness_summaries(session)

    build_by_attempt = {t.attempt_no: t.payload for t in typecheck_summaries}
    correctness_by_attempt = {c.attempt_no: c.payload for c in correctness_summaries}
    meta_by_attempt = {a.attempt_no: a.payload for a in attempts}

    all_attempt_nos = sorted(set(build_by_attempt.keys()) | set(correctness_by_attempt.keys()) | set(meta_by_attempt.keys()))

    inferrer_attempts = []
    
    total_attempts = len(all_attempt_nos)
    validation_failed = 0
    build_passed = 0
    build_failed = 0
    pbt_failures = 0

    correctness_triggered = 0
    correctness_ok = 0
    correctness_issues = 0
    correctness_inconclusive = 0
    counterexamples_found = 0

    for att_no in all_attempt_nos:
        t_summary = build_by_attempt.get(att_no)
        c_summary = correctness_by_attempt.get(att_no)
        m_result = meta_by_attempt.get(att_no)

        v_passed = False
        b_passed = False
        p_failure = False
        prog = ""

        if t_summary:
            v_passed = t_summary.validation_passed
            b_passed = t_summary.build_passed
            p_failure = t_summary.pbt_failure
            prog = t_summary.program
            
            if not v_passed:
                validation_failed += 1
            else:
                if b_passed:
                    build_passed += 1
                else:
                    build_failed += 1
            
            if p_failure:
                pbt_failures += 1

        c_verdict_str = None
        ce_found = False
        
        if c_summary:
            correctness_triggered += 1
            c_verdict_str = c_summary.verdict.value
            ce_found = c_summary.counterexample_found
            
            if ce_found:
                counterexamples_found += 1
                
            if c_verdict_str == "ok":
                correctness_ok += 1
            elif c_verdict_str == "issues":
                correctness_issues += 1
            elif c_verdict_str == "inconclusive":
                correctness_inconclusive += 1

        outcome_str = m_result.final_outcome.value if m_result else None

        inferrer_attempts.append(
            InferrerAttempt(
                attempt_no=att_no,
                validation_passed=v_passed,
                build_passed=b_passed,
                pbt_failure=p_failure,
                correctness_verdict=c_verdict_str,
                counterexample_found=ce_found,
                program=prog,
                outcome=outcome_str,
            )
        )

    if attempts:
        last_attempt = max(attempts, key=lambda a: a.attempt_no)
        final_outcome = last_attempt.payload.final_outcome.value
    else:
        final_outcome = "N/A (No attempts found)"

    build_stats = InferrerBuildStats(
        total_attempts=total_attempts,
        validation_failed=validation_failed,
        build_passed=build_passed,
        build_failed=build_failed,
        pbt_failures=pbt_failures,
    )

    correctness_stats = InferrerCorrectnessStats(
        triggered=correctness_triggered,
        ok=correctness_ok,
        issues=correctness_issues,
        inconclusive=correctness_inconclusive,
        counterexamples_found=counterexamples_found,
    )

    return InferrerEffectivenessReport(
        session=session,
        build_stats=build_stats,
        correctness_stats=correctness_stats,
        final_outcome=final_outcome,
        attempts=inferrer_attempts,
    )


def evaluate_programmer_effectiveness(session: str) -> ProgrammerEffectivenessReport:
    attempts = programmer_query_attempt_meta(session)
    typecheck_summaries = programmer_query_typecheck_summaries(session)
    judge_results = programmer_query_judge_results(session)

    build_by_attempt = {t.attempt_no: t.payload for t in typecheck_summaries}
    judge_by_attempt = {j.attempt_no: j.payload for j in judge_results}
    meta_by_attempt = {a.attempt_no: a.payload for a in attempts}

    all_attempt_nos = sorted(set(build_by_attempt.keys()) | set(judge_by_attempt.keys()) | set(meta_by_attempt.keys()))

    programmer_attempts = []
    
    total_attempts = len(all_attempt_nos)
    build_passed = 0
    build_failed = 0
    assertion_failures = 0
    pbt_failures = 0

    judge_triggered = 0
    judge_passed = 0
    judge_failed = 0

    for att_no in all_attempt_nos:
        t_summary = build_by_attempt.get(att_no)
        j_result = judge_by_attempt.get(att_no)
        m_result = meta_by_attempt.get(att_no)

        b_passed = False
        a_failure = False
        p_failure = False
        prog = ""

        if t_summary:
            b_passed = t_summary.build_passed
            a_failure = t_summary.assertion_failure
            p_failure = t_summary.pbt_failure
            prog = t_summary.program
            
            if b_passed:
                build_passed += 1
            else:
                build_failed += 1
            
            if a_failure:
                assertion_failures += 1
            
            if p_failure:
                pbt_failures += 1

        j_verdict_str = None
        if j_result:
            j_verdict_str = j_result.verdict.value
            judge_triggered += 1
            if j_result.verdict == JudgeVerdict.PASS:
                judge_passed += 1
            else:
                judge_failed += 1
            
            if not prog and j_result.program:
                prog = j_result.program

        outcome_str = m_result.final_outcome.value if m_result else None

        programmer_attempts.append(
            ProgrammerAttempt(
                attempt_no=att_no,
                build_passed=b_passed,
                assertion_failure=a_failure,
                pbt_failure=p_failure,
                judge_verdict=j_verdict_str,
                program=prog,
                outcome=outcome_str,
            )
        )

    if attempts:
        last_attempt = max(attempts, key=lambda a: a.attempt_no)
        final_outcome = last_attempt.payload.final_outcome.value
    else:
        final_outcome = "N/A (No attempts found)"

    build_stats = ProgrammerBuildStats(
        total_attempts=total_attempts,
        build_passed=build_passed,
        build_failed=build_failed,
        assertion_failures=assertion_failures,
        pbt_failures=pbt_failures,
    )

    judge_stats = ProgrammerJudgeStats(
        triggered=judge_triggered,
        passed=judge_passed,
        failed=judge_failed,
    )

    return ProgrammerEffectivenessReport(
        session=session,
        build_stats=build_stats,
        judge_stats=judge_stats,
        final_outcome=final_outcome,
        attempts=programmer_attempts,
    )


def evaluate_lean_synth_effectiveness(session: str) -> LeanSynthEffectivenessReport:
    attempts = lean_synth_query_attempt_meta(session)
    typecheck_summaries = lean_synth_query_typecheck_summaries(session)
    judge_results = lean_synth_query_judge_results(session)
    proof_summaries = lean_synth_query_proof_summaries(session)

    build_by_attempt = {t.attempt_no: t.payload for t in typecheck_summaries}
    judge_by_attempt = {j.attempt_no: j.payload for j in judge_results}
    proof_by_attempt = {p.attempt_no: p.payload for p in proof_summaries}
    meta_by_attempt = {a.attempt_no: a.payload for a in attempts}

    all_attempt_nos = sorted(
        set(build_by_attempt.keys())
        | set(judge_by_attempt.keys())
        | set(proof_by_attempt.keys())
        | set(meta_by_attempt.keys())
    )

    lean_attempts = []
    total_attempts = len(all_attempt_nos)
    validation_failures = 0
    build_passed = 0
    build_failed = 0
    pbt_failures = 0
    judge_triggered = 0
    judge_passed = 0
    judge_failed = 0
    proof_triggered = 0
    proof_proven = 0
    proof_partial = 0
    proof_failed = 0
    proof_preparation_failed = 0
    final_build_failed = 0

    for att_no in all_attempt_nos:
        t_summary = build_by_attempt.get(att_no)
        j_result = judge_by_attempt.get(att_no)
        p_summary = proof_by_attempt.get(att_no)
        m_result = meta_by_attempt.get(att_no)

        v_passed = False
        b_passed = False
        p_failure = False
        j_verdict_str = None
        proof_status_str = None
        has_sorry = False
        final_build_passed = False
        prog = ""

        if t_summary:
            v_passed = t_summary.validation_passed
            b_passed = t_summary.build_passed
            p_failure = t_summary.pbt_failure
            prog = t_summary.program
            if not v_passed:
                validation_failures += 1
            elif b_passed:
                build_passed += 1
            else:
                build_failed += 1
            if p_failure:
                pbt_failures += 1

        if j_result:
            j_verdict_str = j_result.verdict.value
            judge_triggered += 1
            if j_result.verdict == JudgeVerdict.PASS:
                judge_passed += 1
            else:
                judge_failed += 1
            if not prog and j_result.program:
                prog = j_result.program

        if p_summary:
            proof_triggered += 1
            proof_status_str = p_summary.status.value
            has_sorry = p_summary.has_sorry
            final_build_passed = p_summary.final_build_passed
            if not prog and p_summary.program:
                prog = p_summary.program
            if p_summary.status == LeanSynthProofStatus.PROVEN:
                proof_proven += 1
            elif p_summary.status == LeanSynthProofStatus.PARTIAL:
                proof_partial += 1
            elif p_summary.status == LeanSynthProofStatus.FAILED:
                proof_failed += 1
            elif p_summary.status == LeanSynthProofStatus.PREPARATION_FAILED:
                proof_preparation_failed += 1
            if not p_summary.final_build_passed:
                final_build_failed += 1

        outcome_str = m_result.final_outcome.value if m_result else None

        lean_attempts.append(
            LeanSynthAttempt(
                attempt_no=att_no,
                validation_passed=v_passed,
                build_passed=b_passed,
                pbt_failure=p_failure,
                judge_verdict=j_verdict_str,
                proof_status=proof_status_str,
                has_sorry=has_sorry,
                final_build_passed=final_build_passed,
                program=prog,
                outcome=outcome_str,
            )
        )

    if attempts:
        last_attempt = max(attempts, key=lambda a: a.attempt_no)
        final_outcome = last_attempt.payload.final_outcome.value
    else:
        final_outcome = "N/A (No attempts found)"

    return LeanSynthEffectivenessReport(
        session=session,
        build_stats=LeanSynthBuildStats(
            total_attempts=total_attempts,
            validation_failures=validation_failures,
            build_passed=build_passed,
            build_failed=build_failed,
            pbt_failures=pbt_failures,
        ),
        judge_stats=LeanSynthJudgeStats(
            triggered=judge_triggered,
            passed=judge_passed,
            failed=judge_failed,
        ),
        proof_stats=LeanSynthProofStats(
            triggered=proof_triggered,
            proven=proof_proven,
            partial=proof_partial,
            failed=proof_failed,
            preparation_failed=proof_preparation_failed,
            final_build_failed=final_build_failed,
        ),
        final_outcome=final_outcome,
        attempts=lean_attempts,
    )


def main():
    import argparse
    import json
    import re
    import sys
    from dataclasses import asdict
    from utils.analytics.query import query as run_sql_query
    from scripts.visualize_effectiveness import (
        visualize_specgen_session, 
        visualize_specgen_aggregate,
        visualize_programmer_session,
        visualize_programmer_aggregate,
        visualize_lean_synth_session,
        visualize_lean_synth_aggregate,
    )

    parser = argparse.ArgumentParser(description="Evaluate agent effectiveness.")
    parser.add_argument("agent", choices=["specgen", "programmer", "inferrer", "lean-synth"], help="The agent to evaluate")
    parser.add_argument("--session", type=str, help="Specific session to evaluate (if not provided, evaluates all sessions)")
    parser.add_argument(
        "--session-pattern",
        type=str,
        help="Regex used to filter session names before evaluation",
    )
    parser.add_argument("--view", choices=["session", "aggregate", "both"], default="both", help="How to display the results")
    parser.add_argument("--output", type=str, help="Output JSON file path")
    
    args = parser.parse_args()

    session_pattern = None
    if args.session_pattern:
        try:
            session_pattern = re.compile(args.session_pattern)
        except re.error as exc:
            print(f"Invalid regex for --session-pattern: {exc}", file=sys.stderr)
            raise SystemExit(2) from exc
    
    sessions = []
    if args.session:
        sessions = [args.session]
    else:
        rows = run_sql_query("SELECT DISTINCT session_name FROM attempt_records")
        sessions = [row["session_name"] for row in rows if "session_name" in row]
        if not sessions:
            print("No sessions found in the database.")
            return

    if session_pattern:
        sessions = [session for session in sessions if session_pattern.search(session)]
        if not sessions:
            print(f"No sessions matched --session-pattern {args.session_pattern!r}.")
            return

    results = []
    for sess in sessions:
        if args.agent == "specgen":
            res = evaluate_specgen_effectivess(sess)
            results.append(res)
        elif args.agent == "programmer":
            res = evaluate_programmer_effectiveness(sess)
            results.append(res)
        elif args.agent == "inferrer":
            res = evaluate_inferrer_effectiveness(sess)
            results.append(res)
        elif args.agent == "lean-synth":
            res = evaluate_lean_synth_effectiveness(sess)
            results.append(res)

    if args.agent == "specgen" and results:
        if args.view in ["session", "both"]:
            for res in results:
                visualize_specgen_session(res)
        
        if args.view in ["aggregate", "both"] and len(results) > 1:
            visualize_specgen_aggregate(results)
        elif args.view == "aggregate" and len(results) == 1:
            visualize_specgen_session(results[0])

    elif args.agent == "programmer" and results:
        if args.view in ["session", "both"]:
            for res in results:
                visualize_programmer_session(res)
        
        if args.view in ["aggregate", "both"] and len(results) > 1:
            visualize_programmer_aggregate(results)
        elif args.view == "aggregate" and len(results) == 1:
            visualize_programmer_session(results[0])

    elif args.agent == "inferrer" and results:
        from scripts.visualize_effectiveness import visualize_inferrer_session, visualize_inferrer_aggregate
        if args.view in ["session", "both"]:
            for res in results:
                visualize_inferrer_session(res)
        
        if args.view in ["aggregate", "both"] and len(results) > 1:
            visualize_inferrer_aggregate(results)
        elif args.view == "aggregate" and len(results) == 1:
            visualize_inferrer_session(results[0])

    elif args.agent == "lean-synth" and results:
        if args.view in ["session", "both"]:
            for res in results:
                visualize_lean_synth_session(res)

        if args.view in ["aggregate", "both"] and len(results) > 1:
            visualize_lean_synth_aggregate(results)
        elif args.view == "aggregate" and len(results) == 1:
            visualize_lean_synth_session(results[0])

    if args.output and results:
        # Convert dataclasses to dicts for JSON
        dict_results = [asdict(r) for r in results]
        with open(args.output, "w") as f:
            json.dump(dict_results, f, indent=2)
        print(f"\nResults saved to {args.output}")

if __name__ == "__main__":
    main()
