import hashlib
import importlib
import json
from pathlib import Path

import pytest
from langchain_core.messages import AIMessage

from ..planner import PlanError, compile_plan, generate_plan, load_plan


def _specification(method: str) -> str:
    return f"""=== TASK_DESCRIPTION ===
Implement the pure {method} method for natural numbers.

=== METHOD_SIGNATURE ===
method {method}(value: Nat) returns (result: Nat)

=== TEST_CASES ===
{{"test_1": {{"input": {{"value": 1}}, "expected": 1}}}}
"""


def _write_plan(tmp_path: Path) -> Path:
    source = tmp_path / "project.txt"
    source.write_text("Implement two numeric methods.\n", encoding="utf-8")
    specs = tmp_path / "specs"
    specs.mkdir()
    (specs / "alpha.txt").write_text(_specification("alpha"), encoding="utf-8")
    (specs / "beta.txt").write_text(_specification("beta"), encoding="utf-8")
    plan_file = tmp_path / "plan.json"
    plan_file.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "project_id": "tiny-plan",
                "source_file": "project.txt",
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "tasks": [
                    {
                        "id": "beta",
                        "input_file": "specs/beta.txt",
                        "output_file": "artifacts/Beta.lean",
                        "depends_on": ["alpha"],
                    },
                    {
                        "id": "alpha",
                        "input_file": "specs/alpha.txt",
                        "output_file": "artifacts/Alpha.lean",
                        "depends_on": [],
                    },
                ],
            }
        ),
        encoding="utf-8",
    )
    return plan_file


def test_compile_plan_hashes_reviewed_task_files(tmp_path: Path):
    plan_file = _write_plan(tmp_path)

    manifest = compile_plan(plan_file)

    assert [task.id for task in manifest.execution_order()] == ["alpha", "beta"]
    assert manifest.manifest_file == tmp_path / "job.json"
    assert manifest.tasks[0].input_sha256 == hashlib.sha256(
        (tmp_path / "specs" / "beta.txt").read_bytes()
    ).hexdigest()


def test_load_plan_rejects_changed_project_source(tmp_path: Path):
    plan_file = _write_plan(tmp_path)
    (tmp_path / "project.txt").write_text("changed\n", encoding="utf-8")

    with pytest.raises(PlanError, match="source_sha256 does not match"):
        load_plan(plan_file)


def test_load_plan_rejects_multi_method_task(tmp_path: Path):
    plan_file = _write_plan(tmp_path)
    spec = tmp_path / "specs" / "alpha.txt"
    spec.write_text(
        _specification("alpha").replace(
            "=== TEST_CASES ===",
            "method extra(value: Nat) returns (result: Nat)\n\n"
            "=== TEST_CASES ===",
        ),
        encoding="utf-8",
    )

    with pytest.raises(PlanError, match="exactly one method signature"):
        load_plan(plan_file)


@pytest.mark.asyncio
async def test_generate_plan_writes_human_reviewable_files(
    monkeypatch,
    tmp_path: Path,
):
    source = tmp_path / "request.txt"
    source.write_text("Implement alpha and beta.\n", encoding="utf-8")
    response = {
        "tasks": [
            {
                "id": "alpha",
                "depends_on": [],
                "specification": _specification("alpha"),
            },
            {
                "id": "beta",
                "depends_on": ["alpha"],
                "specification": _specification("beta"),
            },
        ]
    }

    class FakeLLM:
        async def ainvoke(self, _messages):
            return AIMessage(content=json.dumps(response))

    providers = importlib.import_module("providers")
    token_tracker = importlib.import_module("utils.token_tracker")

    monkeypatch.setattr(providers, "get_llm", lambda *_args, **_kwargs: FakeLLM())
    monkeypatch.setattr(token_tracker, "check_limits_before_llm_call", lambda: None)
    monkeypatch.setattr(token_tracker, "set_current_agent", lambda _name: None)

    plan = await generate_plan(
        source,
        tmp_path / "generated",
        project_id="tiny",
        provider="openai",
        model="model",
    )

    assert plan.plan_file.is_file()
    assert [task.id for task in plan.execution_order()] == ["alpha", "beta"]
    assert plan.tasks[0].input_file.read_text().startswith(
        "=== TASK_DESCRIPTION ==="
    )
