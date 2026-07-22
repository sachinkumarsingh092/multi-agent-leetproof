import json
import sys
from pathlib import Path

import pytest

from cli import run_query
from utils.analytics.query import execute_query_operation, list_query_operations
from utils.analytics.store import AnalyticsStore
from utils.analytics.velvet_programmer import (
    PBTStatus,
    TypecheckSummary,
    write_typecheck_summary,
)
from utils.analytics.lean_synth_and_verify import (
    TypecheckSummary as LeanSynthTypecheckSummary,
    write_typecheck_summary as write_lean_synth_typecheck_summary,
)


def test_list_query_operations_includes_agent_helpers():
    operations = {operation.name: operation for operation in list_query_operations()}
    assert "general.query_records" in operations
    assert "velvet_programmer.query_typecheck_summaries" in operations
    assert "velvet_programmer.query_judge_results" in operations
    assert "velvet_programmer.query_attempt_meta" in operations
    assert "velvet_invariant_inferrer.query_typecheck_summaries" in operations
    assert "velvet_invariant_inferrer.query_correctness_summaries" in operations
    assert "lean_synth_and_verify.query_typecheck_summaries" in operations
    assert "lean_synth_and_verify.query_judge_results" in operations
    assert "lean_synth_and_verify.query_proof_summaries" in operations
    assert "lean_synth_and_verify.query_attempt_meta" in operations

    general_records = operations["general.query_records"]
    assert general_records.required_parameters == ["session_name"]
    assert general_records.optional_parameters == ["scope", "attempt_no", "key"]

    programmer_typecheck = operations["velvet_programmer.query_typecheck_summaries"]
    assert programmer_typecheck.required_parameters == ["session_name"]
    assert programmer_typecheck.optional_parameters == []


def test_execute_query_operation_returns_json_ready_payload(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.velvet_programmer.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("velvet_programmer", 3, session_name="session-op")
    write_typecheck_summary(
        attempt_log,
        TypecheckSummary(
            build_passed=True,
            pbt_failure=False,
            assertion_failure=False,
            program="prog",
            impl_section="impl",
            pbt_status=PBTStatus.NOT_ATTEMPTED,
            pbt_failure_message=None,
        ),
        text="all good",
    )

    result = execute_query_operation(
        "velvet_programmer.query_typecheck_summaries",
        {"session_name": "session-op"},
    )

    assert isinstance(result, list)
    assert result == [
        {
            "session_name": "session-op",
            "scope": "velvet_programmer",
            "attempt_no": 3,
            "key": "summary.typecheck",
            "payload": {
                "build_passed": True,
                "pbt_failure": False,
                "assertion_failure": False,
                "program": "prog",
                "impl_section": "impl",
                "pbt_status": "NOT_ATTEMPTED",
                "pbt_failure_message": None,
            },
            "text_content": "all good",
        }
    ]


def test_execute_general_query_operation_filters_rows(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.general.get_analytics_store",
        lambda: store,
    )

    attempt_one = store.attempt("worker", 1, session_name="session-general")
    write_typecheck_summary(
        attempt_one,
        TypecheckSummary(
            build_passed=True,
            pbt_failure=False,
            assertion_failure=False,
            program="prog-a",
            impl_section="impl-a",
            pbt_status=PBTStatus.NOT_ATTEMPTED,
            pbt_failure_message=None,
        ),
        text="log-a",
    )
    attempt_two = store.attempt("worker", 2, session_name="session-general")
    attempt_two.put("attempt.meta", {"final_outcome": "ok", "reasoning_level": "low"})

    result = execute_query_operation(
        "general.query_records",
        {"session_name": "session-general", "scope": "worker", "attempt_no": 2},
    )

    assert result == [
        {
            "session_name": "session-general",
            "scope": "worker",
            "attempt_no": 2,
            "key": "attempt.meta",
            "payload": {"final_outcome": "ok", "reasoning_level": "low"},
            "text_content": None,
        }
    ]


def test_run_query_operation_mode_prints_json(monkeypatch, tmp_path: Path, capsys):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.velvet_programmer.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("velvet_programmer", 5, session_name="session-cli")
    write_typecheck_summary(
        attempt_log,
        TypecheckSummary(
            build_passed=False,
            pbt_failure=True,
            assertion_failure=False,
            program="prog2",
            impl_section="impl2",
            pbt_status=PBTStatus.ADDED_COMPILE_FAILED,
            pbt_failure_message="cex",
        ),
        text="build log text",
    )

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "lloom-agent",
            "query",
            "--project",
            str(tmp_path),
            "--operation",
            "velvet_programmer.query_typecheck_summaries",
            "--input",
            json.dumps({"session_name": "session-cli"}),
        ],
    )

    run_query()
    output = json.loads(capsys.readouterr().out)

    assert output[0]["session_name"] == "session-cli"
    assert output[0]["attempt_no"] == 5
    assert output[0]["payload"]["pbt_status"] == "ADDED_COMPILE_FAILED"
    assert output[0]["text_content"] == "build log text"


def test_execute_lean_synth_query_operation_returns_json_ready_payload(monkeypatch, tmp_path: Path):
    store = AnalyticsStore(tmp_path / "analytics.sqlite")
    monkeypatch.setattr(
        "utils.analytics.lean_synth_and_verify.get_analytics_store",
        lambda: store,
    )

    attempt_log = store.attempt("lean_synth_and_verify", 2, session_name="session-lean-op")
    write_lean_synth_typecheck_summary(
        attempt_log,
        LeanSynthTypecheckSummary(
            validation_passed=True,
            build_passed=False,
            pbt_failure=True,
            program="prog",
            impl_section="impl",
            pbt_status=PBTStatus.ADDED_AND_PASSED,
            pbt_failure_message="counterexample",
        ),
        text="lean build log",
    )

    result = execute_query_operation(
        "lean_synth_and_verify.query_typecheck_summaries",
        {"session_name": "session-lean-op"},
    )

    assert result == [
        {
            "session_name": "session-lean-op",
            "scope": "lean_synth_and_verify",
            "attempt_no": 2,
            "key": "summary.typecheck",
            "payload": {
                "validation_passed": True,
                "build_passed": False,
                "pbt_failure": True,
                "program": "prog",
                "impl_section": "impl",
                "pbt_status": "ADDED_AND_PASSED",
                "pbt_failure_message": "counterexample",
            },
            "text_content": "lean build log",
        }
    ]


def test_run_query_requires_json_object_input(monkeypatch, tmp_path: Path):
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "lloom-agent",
            "query",
            "--project",
            str(tmp_path),
            "--operation",
            "velvet_programmer.query_typecheck_summaries",
            "--input",
            "[]",
        ],
    )

    with pytest.raises(SystemExit):
        run_query()
