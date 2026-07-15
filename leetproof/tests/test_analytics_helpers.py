from pathlib import Path

from agents.spec_state import CoachVerdict
from utils.analytics.spec_generation import (
    AttemptMeta as SpecAttemptMeta,
    AttemptOutcome as SpecAttemptOutcome,
    CoachReview,
    PBTSummary,
    SpecPBTResult,
    TypecheckSummary as SpecTypecheckSummary,
    query_attempt_meta as query_spec_attempt_meta,
    query_coach_reviews,
    query_pbt_summaries,
    query_typecheck_summaries as query_spec_typecheck_summaries,
    write_attempt_meta as write_spec_attempt_meta,
    write_coach_review,
    write_pbt_summary,
    write_typecheck_summary as write_spec_typecheck_summary,
)
from utils.analytics.store import AnalyticsStore
from utils.analytics.velvet_invariant_inferrer import (
    AttemptMeta as InferrerAttemptMeta,
    AttemptOutcome as InferrerAttemptOutcome,
    CorrectnessGoalKind,
    CorrectnessSummary,
    CorrectnessVerdict,
    LLMGoalResult,
    TypecheckSummary as InferrerTypecheckSummary,
    query_attempt_meta as query_inferrer_attempt_meta,
    query_correctness_summaries,
    query_typecheck_summaries as query_inferrer_typecheck_summaries,
    write_attempt_meta as write_inferrer_attempt_meta,
    write_correctness_summary,
    write_typecheck_summary as write_inferrer_typecheck_summary,
)
from utils.analytics.velvet_programmer import (
    AttemptMeta as ProgrammerAttemptMeta,
    AttemptOutcome as ProgrammerAttemptOutcome,
    JudgeResult,
    JudgeVerdict,
    PBTStatus,
    TypecheckSummary as ProgrammerTypecheckSummary,
    query_attempt_meta as query_programmer_attempt_meta,
    query_judge_results,
    query_typecheck_summaries as query_programmer_typecheck_summaries,
    write_attempt_meta as write_programmer_attempt_meta,
    write_judge_result,
    write_typecheck_summary as write_programmer_typecheck_summary,
)
from utils.analytics.lean_synth_and_verify import (
    AttemptMeta as LeanSynthAttemptMeta,
    AttemptOutcome as LeanSynthAttemptOutcome,
    JudgeResult as LeanSynthJudgeResult,
    ProofStatus,
    ProofSummary,
    TypecheckSummary as LeanSynthTypecheckSummary,
    query_attempt_meta as query_lean_synth_attempt_meta,
    query_judge_results as query_lean_synth_judge_results,
    query_proof_summaries,
    query_typecheck_summaries as query_lean_synth_typecheck_summaries,
    write_attempt_meta as write_lean_synth_attempt_meta,
    write_judge_result as write_lean_synth_judge_result,
    write_proof_summary,
    write_typecheck_summary as write_lean_synth_typecheck_summary,
)


def test_spec_generation_analytics_write_and_read(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.spec_generation.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("spec_generation", 1, session_name="session-spec")

    write_spec_typecheck_summary(
        attempt_log,
        SpecTypecheckSummary(
            build_passed=False,
            has_axiom=False,
            sorry_count=1,
            extracted_goals_typecheck_passed=True,
            spec="full spec file",
            specs_section="section Specs\n...\nend Specs",
            impl_section="section Impl\n...\nend Impl",
            testcases_section="section TestCases\n...\nend TestCases",
        ),
        text="typecheck log",
    )
    write_pbt_summary(
        attempt_log,
        PBTSummary(enabled=True, result=SpecPBTResult.POSTCOND_BUG),
        text="pbt detail",
    )
    write_coach_review(
        attempt_log,
        CoachReview(verdict=CoachVerdict.REJECT, score=17),
        text="coach feedback",
    )
    write_spec_attempt_meta(
        attempt_log,
        SpecAttemptMeta(
            final_outcome=SpecAttemptOutcome.PBT_BUG,
            file_path="test.lean",
            reasoning_level=None,
            error_message="pbt detail",
        ),
    )

    typecheck_rows = query_spec_typecheck_summaries("session-spec")
    assert len(typecheck_rows) == 1
    assert typecheck_rows[0].attempt_no == 1
    assert typecheck_rows[0].payload == SpecTypecheckSummary(
        build_passed=False,
        has_axiom=False,
        sorry_count=1,
        extracted_goals_typecheck_passed=True,
        spec="full spec file",
        specs_section="section Specs\n...\nend Specs",
        impl_section="section Impl\n...\nend Impl",
        testcases_section="section TestCases\n...\nend TestCases",
    )
    assert typecheck_rows[0].text_content == "typecheck log"

    pbt_rows = query_pbt_summaries("session-spec")
    assert len(pbt_rows) == 1
    assert pbt_rows[0].payload == PBTSummary(
        enabled=True,
        result=SpecPBTResult.POSTCOND_BUG,
    )
    assert pbt_rows[0].text_content == "pbt detail"

    coach_rows = query_coach_reviews("session-spec")
    assert len(coach_rows) == 1
    assert coach_rows[0].payload == CoachReview(
        verdict=CoachVerdict.REJECT,
        score=17,
    )
    assert coach_rows[0].text_content == "coach feedback"

    meta_rows = query_spec_attempt_meta("session-spec")
    assert len(meta_rows) == 1
    assert meta_rows[0].payload == SpecAttemptMeta(
        final_outcome=SpecAttemptOutcome.PBT_BUG,
        file_path="test.lean",
        reasoning_level=None,
        error_message="pbt detail",
    )


def test_programmer_analytics_write_and_read(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.velvet_programmer.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("velvet_programmer", 1, session_name="session-a")

    write_programmer_typecheck_summary(
        attempt_log,
        ProgrammerTypecheckSummary(
            build_passed=False,
            pbt_failure=True,
            assertion_failure=False,
            program="the full program",
            impl_section="def foo := 1",
            pbt_status=PBTStatus.ADDED_AND_PASSED,
            pbt_failure_message="counterexample found",
        ),
        text="build log",
    )
    write_judge_result(
        attempt_log,
        JudgeResult(
            verdict=JudgeVerdict.PASS,
            reasoning="looks good",
            program="def foo := 1",
        ),
    )
    write_programmer_attempt_meta(
        attempt_log,
        ProgrammerAttemptMeta(
            final_outcome=ProgrammerAttemptOutcome.JUDGE_PASS,
            file_path="prog.lean",
            reasoning_level="low",
        ),
    )

    typecheck_rows = query_programmer_typecheck_summaries("session-a")
    assert len(typecheck_rows) == 1
    assert typecheck_rows[0].attempt_no == 1
    assert typecheck_rows[0].payload == ProgrammerTypecheckSummary(
        build_passed=False,
        pbt_failure=True,
        assertion_failure=False,
        program="the full program",
        impl_section="def foo := 1",
        pbt_status=PBTStatus.ADDED_AND_PASSED,
        pbt_failure_message="counterexample found",
    )
    assert typecheck_rows[0].text_content == "build log"

    judge_rows = query_judge_results("session-a")
    assert len(judge_rows) == 1
    assert judge_rows[0].payload == JudgeResult(
        verdict=JudgeVerdict.PASS,
        reasoning="looks good",
        program="def foo := 1",
    )

    meta_rows = query_programmer_attempt_meta("session-a")
    assert len(meta_rows) == 1
    assert meta_rows[0].payload == ProgrammerAttemptMeta(
        final_outcome=ProgrammerAttemptOutcome.JUDGE_PASS,
        file_path="prog.lean",
        reasoning_level="low",
        error_message=None,
    )


def test_lean_synth_analytics_write_and_read(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.lean_synth_and_verify.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("lean_synth_and_verify", 4, session_name="session-lean")

    write_lean_synth_typecheck_summary(
        attempt_log,
        LeanSynthTypecheckSummary(
            validation_passed=True,
            build_passed=True,
            pbt_failure=False,
            program="def implementation := 1",
            impl_section="section Impl\ndef implementation := 1\nend Impl",
            pbt_status=PBTStatus.ADDED_AND_PASSED,
            pbt_failure_message=None,
        ),
        text="typecheck ok",
    )
    write_lean_synth_judge_result(
        attempt_log,
        LeanSynthJudgeResult(
            verdict=JudgeVerdict.PASS,
            reasoning="good implementation",
            program="def implementation := 1",
        ),
    )
    write_proof_summary(
        attempt_log,
        ProofSummary(
            status=ProofStatus.PROVEN,
            has_sorry=False,
            final_build_passed=True,
            program="full final program",
            error_message=None,
        ),
        text="proof ok",
    )
    write_lean_synth_attempt_meta(
        attempt_log,
        LeanSynthAttemptMeta(
            final_outcome=LeanSynthAttemptOutcome.PROOF_PROVEN,
            file_path="lean.lean",
            reasoning_level="low",
            error_message=None,
        ),
    )

    typecheck_rows = query_lean_synth_typecheck_summaries("session-lean")
    assert len(typecheck_rows) == 1
    assert typecheck_rows[0].payload == LeanSynthTypecheckSummary(
        validation_passed=True,
        build_passed=True,
        pbt_failure=False,
        program="def implementation := 1",
        impl_section="section Impl\ndef implementation := 1\nend Impl",
        pbt_status=PBTStatus.ADDED_AND_PASSED,
        pbt_failure_message=None,
    )
    assert typecheck_rows[0].text_content == "typecheck ok"

    judge_rows = query_lean_synth_judge_results("session-lean")
    assert len(judge_rows) == 1
    assert judge_rows[0].payload == LeanSynthJudgeResult(
        verdict=JudgeVerdict.PASS,
        reasoning="good implementation",
        program="def implementation := 1",
    )

    proof_rows = query_proof_summaries("session-lean")
    assert len(proof_rows) == 1
    assert proof_rows[0].payload == ProofSummary(
        status=ProofStatus.PROVEN,
        has_sorry=False,
        final_build_passed=True,
        program="full final program",
        error_message=None,
    )
    assert proof_rows[0].text_content == "proof ok"

    meta_rows = query_lean_synth_attempt_meta("session-lean")
    assert len(meta_rows) == 1
    assert meta_rows[0].payload == LeanSynthAttemptMeta(
        final_outcome=LeanSynthAttemptOutcome.PROOF_PROVEN,
        file_path="lean.lean",
        reasoning_level="low",
        error_message=None,
    )


def test_inferrer_analytics_write_and_read(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.velvet_invariant_inferrer.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("velvet_invariant_inferrer", 2, session_name="session-b")

    write_inferrer_typecheck_summary(
        attempt_log,
        InferrerTypecheckSummary(
            validation_passed=True,
            build_passed=True,
            pbt_failure=False,
            program="the inferrer program",
            impl_section="method body with invariants",
            pbt_failure_message=None,
        ),
        text="typecheck ok",
    )
    write_correctness_summary(
        attempt_log,
        CorrectnessSummary(
            verdict=CorrectnessVerdict.ISSUES,
            invariant_goal_count=2,
            non_invariant_goal_count=1,
            extracted_goals_typecheck_passed=True,
            counterexample_found=False,
            automation_discharged_invariant_goals=1,
            automation_discharged_non_invariant_goals=0,
            llm_results=[
                LLMGoalResult(
                    kind=CorrectnessGoalKind.INVARIANT,
                    goal_id="g1",
                    label="inv1",
                    goal_statement="theorem g1",
                    is_provable=False,
                    justification="missing hypothesis",
                    correction_hint="strengthen invariant",
                    success=True,
                    error=None,
                )
            ],
        ),
        text="retry this invariant",
    )
    write_inferrer_attempt_meta(
        attempt_log,
        InferrerAttemptMeta(
            final_outcome=InferrerAttemptOutcome.CORRECTNESS_ISSUES,
            file_path="inv.lean",
            reasoning_level="medium",
            error_message="retry this invariant",
        ),
    )

    typecheck_rows = query_inferrer_typecheck_summaries("session-b")
    assert len(typecheck_rows) == 1
    assert typecheck_rows[0].attempt_no == 2
    assert typecheck_rows[0].payload == InferrerTypecheckSummary(
        validation_passed=True,
        build_passed=True,
        pbt_failure=False,
        program="the inferrer program",
        impl_section="method body with invariants",
        pbt_failure_message=None,
    )
    assert typecheck_rows[0].text_content == "typecheck ok"

    correctness_rows = query_correctness_summaries("session-b")
    assert len(correctness_rows) == 1
    assert correctness_rows[0].payload == CorrectnessSummary(
        verdict=CorrectnessVerdict.ISSUES,
        invariant_goal_count=2,
        non_invariant_goal_count=1,
        extracted_goals_typecheck_passed=True,
        counterexample_found=False,
        automation_discharged_invariant_goals=1,
        automation_discharged_non_invariant_goals=0,
        llm_results=[
            LLMGoalResult(
                kind=CorrectnessGoalKind.INVARIANT,
                goal_id="g1",
                label="inv1",
                goal_statement="theorem g1",
                is_provable=False,
                justification="missing hypothesis",
                correction_hint="strengthen invariant",
                success=True,
                error=None,
            )
        ],
    )
    assert correctness_rows[0].text_content == "retry this invariant"

    meta_rows = query_inferrer_attempt_meta("session-b")
    assert len(meta_rows) == 1
    assert meta_rows[0].payload == InferrerAttemptMeta(
        final_outcome=InferrerAttemptOutcome.CORRECTNESS_ISSUES,
        file_path="inv.lean",
        reasoning_level="medium",
        error_message="retry this invariant",
    )
