import argparse
import hashlib
import inspect
import json
import re
import signal
from pathlib import Path

import pytest

import pipeline
import runner
from args import Stage, get_parser, merge_session_params, save_session_params
from pipeline import (
    freeze_formal_contract,
    load_input_for_stage,
    resolve_pipeline_session_name,
    validate_worker_paths,
)


def test_worker_stage_order_starts_from_reviewed_text():
    assert list(Stage) == [
        Stage.SPECGEN,
        Stage.CODEGEN,
        Stage.INVGEN,
        Stage.VERIFY,
    ]


def test_pipeline_cli_defaults_to_current_project_and_generated_session():
    args = get_parser().parse_args([])

    assert args.project == "."
    assert args.session_name is None
    assert re.fullmatch(
        r"pipeline-\d{8}-\d{6}-[0-9a-f]{8}",
        resolve_pipeline_session_name(args.session_name, resume=False),
    )


def test_pipeline_resume_requires_explicit_session_name():
    with pytest.raises(ValueError, match="--resume requires --session-name"):
        resolve_pipeline_session_name(None, resume=True)

    assert (
        resolve_pipeline_session_name("raft-001", resume=True)
        == "raft-001"
    )


def test_specgen_requires_text_input_and_lean_output(tmp_path: Path):
    reviewed_spec = tmp_path / "Specification.txt"
    formal_contract = tmp_path / "Contract.lean"

    validate_worker_paths(
        Stage.SPECGEN,
        str(reviewed_spec),
        str(formal_contract),
    )

    with pytest.raises(ValueError, match=r"reviewed \.txt"):
        validate_worker_paths(
            Stage.SPECGEN,
            str(formal_contract),
            str(tmp_path / "Other.lean"),
        )


def test_specgen_rejects_malformed_reviewed_text(tmp_path: Path):
    reviewed_spec = tmp_path / "Specification.txt"
    reviewed_spec.write_text("Unstructured requirement")
    load_input = inspect.unwrap(load_input_for_stage)

    with pytest.raises(ValueError, match="TASK_DESCRIPTION"):
        load_input(
            Stage.SPECGEN,
            str(reviewed_spec),
            str(tmp_path / "Contract.lean"),
        )


def test_specgen_rejects_multiple_method_signatures(tmp_path: Path):
    content = """=== TASK_DESCRIPTION ===
Implement two operations.
=== METHOD_SIGNATURE ===
method Maximum(a: Nat, b: Nat) returns (result: Nat)
method Minimum(a: Nat, b: Nat) returns (result: Nat)
=== TEST_CASES ===
{"test_1": {"input": {"a": 2, "b": 3}, "expected": 3}}
"""
    reviewed_spec = tmp_path / "Specification.txt"
    reviewed_spec.write_text(content)
    load_input = inspect.unwrap(load_input_for_stage)

    with pytest.raises(ValueError, match="exactly one method signature; found 2"):
        load_input(
            Stage.SPECGEN,
            str(reviewed_spec),
            str(tmp_path / "Contract.lean"),
        )


def test_specgen_loads_reviewed_three_section_format(tmp_path: Path):
    content = """=== TASK_DESCRIPTION ===
Return the larger natural number.
=== METHOD_SIGNATURE ===
method Maximum(a: Nat, b: Nat) returns (result: Nat)
=== TEST_CASES ===
{"test_1": {"input": {"a": 2, "b": 3}, "expected": 3}}
"""
    reviewed_spec = tmp_path / "Specification.txt"
    reviewed_spec.write_text(content)
    load_input = inspect.unwrap(load_input_for_stage)

    state = load_input(
        Stage.SPECGEN,
        str(reviewed_spec),
        str(tmp_path / "Contract.lean"),
    )

    assert state["problem_description"] == content


def test_formal_contract_is_frozen_separately_with_hash(
    monkeypatch, tmp_path: Path
):
    monkeypatch.chdir(tmp_path)
    contract = "section Specs\nend Specs\n"

    artifact, digest = freeze_formal_contract(
        contract,
        "examples/Raft.lean",
        "raft-001",
    )

    artifact_path = Path(artifact)
    assert artifact_path == Path(
        ".lloom/sessions/raft-001/contracts/Raft.contract.lean"
    )
    assert artifact_path.read_text() == contract
    assert digest == hashlib.sha256(contract.encode()).hexdigest()
    assert not Path("examples/Raft.lean").exists()

    assert freeze_formal_contract(
        contract,
        "examples/Raft.lean",
        "raft-001",
    ) == (artifact, digest)
    with pytest.raises(ValueError, match="already frozen"):
        freeze_formal_contract(
            contract + "-- changed\n",
            "examples/Raft.lean",
            "raft-001",
        )


def test_stage_result_exposes_frozen_contract_metadata(
    monkeypatch, tmp_path: Path
):
    result_file = tmp_path / "result.json"
    monkeypatch.setattr(
        pipeline,
        "get_output_result_path",
        lambda _output, _session=None: str(result_file),
    )
    initialize_result = inspect.unwrap(pipeline.initialize_pipeline_result)
    write_result = inspect.unwrap(pipeline.write_stage_result)
    initialize_result(
        "examples/raft.txt",
        "examples/Raft.lean",
        Stage.SPECGEN,
        Stage.VERIFY,
        "raft-001",
    )

    write_result(
        "examples/Raft.lean",
        Stage.SPECGEN,
        {
            "typechecks": True,
            "formal_contract_file": (
                ".lloom/sessions/raft-001/contracts/Raft.contract.lean"
            ),
            "formal_contract_sha256": "abc123",
        },
        "raft-001",
    )

    result = json.loads(result_file.read_text())
    assert result["schema_version"] == pipeline.RESULT_SCHEMA_VERSION
    assert result["session_name"] == "raft-001"
    assert result["status"] == "RUNNING"
    assert result["contract"] == {
        "file": ".lloom/sessions/raft-001/contracts/Raft.contract.lean",
        "sha256": "abc123",
    }
    assert result["stages"]["specgen"] == {
        "status": "SUCCESS",
        "typechecks": True,
    }


def test_success_result_summarizes_verification_and_hash(
    monkeypatch, tmp_path: Path
):
    result_file = tmp_path / "result.json"
    output_file = tmp_path / "Raft.lean"
    output_file.write_text("verified implementation\n")
    monkeypatch.setattr(
        pipeline,
        "get_output_result_path",
        lambda _output, _session=None: str(result_file),
    )
    initialize_result = inspect.unwrap(pipeline.initialize_pipeline_result)
    write_result = inspect.unwrap(pipeline.write_stage_result)
    finalize_result = inspect.unwrap(pipeline.finalize_pipeline_result)
    initialize_result(
        "raft.txt",
        str(output_file),
        Stage.CODEGEN,
        Stage.VERIFY,
        "raft-001",
    )
    write_result(
        str(output_file),
        Stage.CODEGEN,
        {
            "typechecks": True,
            "judge_verdict": pipeline.JudgeVerdict.PASS,
            "pbt_status": pipeline.PBTStatus.ADDED_AND_PASSED,
        },
        "raft-001",
    )
    write_result(
        str(output_file),
        Stage.VERIFY,
        {
            "typechecks": True,
            "output_file": str(output_file),
            "goals": [
                {"status": pipeline.GoalStatus.PROVEN},
                {"status": pipeline.GoalStatus.PROVEN},
            ],
        },
        "raft-001",
    )
    finalize_result(str(output_file), Stage.VERIFY, "raft-001")

    result = json.loads(result_file.read_text())
    assert result["status"] == "SUCCESS"
    assert result["implementation"] == {
        "file": str(output_file),
        "sha256": hashlib.sha256(output_file.read_bytes()).hexdigest(),
    }
    assert result["verification"] == {
        "testcases_passed": True,
        "pbt_status": "ADDED_AND_PASSED",
        "proof_status": "PASSED",
        "goals_proven": 2,
        "goals_partial": 0,
        "goals_total": 2,
    }
    assert result["error"] is None


def test_failure_result_is_structured_and_keeps_partial_artifact(
    monkeypatch, tmp_path: Path
):
    result_file = tmp_path / "result.json"
    output_file = tmp_path / "Raft.lean"
    output_file.write_text("partial implementation\n")
    monkeypatch.setattr(
        pipeline,
        "get_output_result_path",
        lambda _output, _session=None: str(result_file),
    )
    initialize_result = inspect.unwrap(pipeline.initialize_pipeline_result)
    fail_result = inspect.unwrap(pipeline.fail_pipeline_result)
    initialize_result(
        "raft.txt",
        str(output_file),
        Stage.SPECGEN,
        Stage.VERIFY,
        "raft-001",
    )
    fail_result(
        str(output_file),
        "raft-001",
        Stage.CODEGEN,
        "RuntimeError",
        "model request failed",
    )

    result = json.loads(result_file.read_text())
    assert result["status"] == "FAILED"
    assert result["stages"]["codegen"]["status"] == "FAILED"
    assert result["error"] == {
        "stage": "codegen",
        "type": "RuntimeError",
        "message": "model request failed",
    }
    assert result["implementation"]["sha256"] == hashlib.sha256(
        output_file.read_bytes()
    ).hexdigest()


def test_verify_rejects_typechecking_partial_proof(tmp_path: Path):
    output_file = tmp_path / "Partial.lean"
    output_file.write_text("theorem incomplete : True := by sorry\n")
    state = {
        "typechecks": True,
        "output_file": str(output_file),
        "goals": [{"status": pipeline.GoalStatus.PARTIAL}],
    }

    assert pipeline.check_stage_failed(Stage.VERIFY, state)


@pytest.mark.asyncio
async def test_pipeline_writes_failure_result_for_invalid_input(
    monkeypatch, tmp_path: Path
):
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        pipeline,
        "initialize_pipeline_result",
        inspect.unwrap(pipeline.initialize_pipeline_result),
    )
    monkeypatch.setattr(
        pipeline,
        "fail_pipeline_result",
        inspect.unwrap(pipeline.fail_pipeline_result),
    )
    run_pipeline = inspect.unwrap(pipeline.run_pipeline)

    with pytest.raises(FileNotFoundError):
        await run_pipeline(
            start_stage=Stage.SPECGEN,
            end_stage=Stage.VERIFY,
            input_file="missing.txt",
            output_file="Missing.lean",
            provider="openai",
            model="test-model",
            session_name="failure-001",
        )

    result_file = (
        tmp_path
        / ".lloom"
        / "sessions"
        / "failure-001"
        / "Missing_result.json"
    )
    result = json.loads(result_file.read_text())
    assert result["status"] == "FAILED"
    assert result["error"]["stage"] is None
    assert result["error"]["type"] == "FileNotFoundError"


@pytest.mark.asyncio
async def test_pipeline_rejected_stage_exits_with_failure_result(
    monkeypatch, tmp_path: Path
):
    monkeypatch.chdir(tmp_path)
    input_file = tmp_path / "Contract.lean"
    output_file = tmp_path / "Candidate.lean"
    input_file.write_text("formal contract\n")

    async def reject_codegen(state):
        output_file.write_text("invalid candidate\n")
        return {
            **state,
            "typechecks": False,
            "build_log": "Lean compilation failed",
        }

    for function_name in (
        "initialize_pipeline_result",
        "write_stage_result",
        "fail_pipeline_result",
    ):
        monkeypatch.setattr(
            pipeline,
            function_name,
            inspect.unwrap(getattr(pipeline, function_name)),
        )
    monkeypatch.setattr(pipeline, "run_code_generation", reject_codegen)
    run_pipeline = inspect.unwrap(pipeline.run_pipeline)

    with pytest.raises(pipeline.PipelineStageError):
        await run_pipeline(
            start_stage=Stage.CODEGEN,
            end_stage=Stage.CODEGEN,
            input_file=str(input_file),
            output_file=str(output_file),
            provider="openai",
            model="test-model",
            session_name="rejected-001",
        )

    result_file = (
        tmp_path
        / ".lloom"
        / "sessions"
        / "rejected-001"
        / "Candidate_result.json"
    )
    result = json.loads(result_file.read_text())
    assert result["status"] == "FAILED"
    assert result["stages"]["codegen"]["status"] == "FAILED"
    assert result["error"] == {
        "stage": "codegen",
        "type": "PipelineStageError",
        "message": "Lean compilation failed",
    }


@pytest.mark.asyncio
async def test_spec_generation_preserves_contract_when_output_changes(
    monkeypatch, tmp_path: Path
):
    monkeypatch.chdir(tmp_path)
    contract = "formal contract\n"

    async def fake_generate_contract(
        reviewed_specification,
        output_path,
        project_root,
        config,
    ):
        assert reviewed_specification == "reviewed requirement"
        assert project_root == tmp_path.resolve()
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(contract)
        return contract

    monkeypatch.setattr(
        "formalize.generate_contract",
        fake_generate_contract,
    )
    state = await pipeline.run_spec_generation(
        {
            "problem_description": "reviewed requirement",
            "output_file": "examples/Raft.lean",
        },
        "openai",
        "test-model",
        "raft-001",
    )

    frozen_path = Path(state["formal_contract_file"])
    assert frozen_path.read_text() == contract
    assert state["formal_contract_sha256"] == hashlib.sha256(
        contract.encode()
    ).hexdigest()

    Path("examples/Raft.lean").write_text("generated implementation\n")
    assert frozen_path.read_text() == contract


def test_codegen_rejects_overwriting_frozen_contract(tmp_path: Path):
    contract = tmp_path / "Contract.lean"

    with pytest.raises(ValueError, match="must differ"):
        validate_worker_paths(Stage.CODEGEN, str(contract), str(contract))


def test_later_stages_allow_updating_existing_implementation(tmp_path: Path):
    implementation = tmp_path / "Implementation.lean"

    validate_worker_paths(
        Stage.INVGEN,
        str(implementation),
        str(implementation),
    )
    validate_worker_paths(
        Stage.VERIFY,
        str(implementation),
        str(implementation),
    )


def test_first_signal_requests_graceful_shutdown(monkeypatch):
    installed_handlers = {}
    requests = []

    monkeypatch.setattr(signal, "getsignal", lambda handled_signal: handled_signal)
    monkeypatch.setattr(
        signal,
        "signal",
        lambda handled_signal, handler: installed_handlers.__setitem__(
            handled_signal, handler
        ),
    )
    monkeypatch.setattr(runner, "is_shutdown_requested", lambda: False)
    monkeypatch.setattr(
        runner,
        "request_shutdown",
        lambda reason, run_hooks: requests.append((reason, run_hooks)),
    )

    previous_handlers = runner._install_signal_handlers()
    installed_handlers[signal.SIGTERM](signal.SIGTERM, None)

    assert previous_handlers == {
        signal.SIGINT: signal.SIGINT,
        signal.SIGTERM: signal.SIGTERM,
    }
    assert requests == [("SIGTERM", False)]


def test_resume_restores_pipeline_stage_range(monkeypatch, tmp_path: Path):
    monkeypatch.chdir(tmp_path)
    save_session_params(
        session_name="partial-worker",
        provider="anthropic",
        model="model",
        input_file="Implementation.lean",
        output_file="Implementation.lean",
        start=Stage.INVGEN.value,
        end=Stage.INVGEN.value,
    )
    args = argparse.Namespace(
        resume=True,
        session_name="partial-worker",
        provider=None,
        model=None,
        input_file=None,
        output_file=None,
        start=Stage.SPECGEN.value,
        end=None,
        max_input_tokens=None,
        max_output_tokens=None,
        max_total_tokens=None,
        max_cost=None,
        agent_context=None,
        prover_v2_max_iterations=None,
    )

    merge_session_params(args)

    assert args.start == Stage.INVGEN.value
    assert args.end == Stage.INVGEN.value
