from pathlib import Path

import pytest
from langchain_core.messages import AIMessage

import prepare
from prepare import RequirementsReviewApp, _parser, normalize_requirements_text
from providers import LLMConfig
from requirements import REQUIRED_SECTIONS, validate_requirements


TEST_CONFIG = LLMConfig(provider="openai", model="test-model")

VALID_REQUIREMENTS = """=== TASK_DESCRIPTION ===
Return the larger of two natural numbers. Inputs are unrestricted natural
numbers, and equal inputs return that same value.

=== METHOD_SIGNATURE ===
method Maximum(a: Nat, b: Nat) returns (result: Nat)

=== TEST_CASES ===
{
  "test_1": {"input": {"a": 2, "b": 3}, "expected": 3},
  "test_2": {"input": {"a": 0, "b": 0}, "expected": 0}
}"""

REVISED_REQUIREMENTS = VALID_REQUIREMENTS.replace(
    "Inputs are unrestricted natural\nnumbers",
    "Inputs must both be positive natural\nnumbers",
)


def test_normalize_requirements_text_removes_text_fence():
    response = f"```text\n{VALID_REQUIREMENTS}\n```"

    assert normalize_requirements_text(response) == VALID_REQUIREMENTS


def test_validate_requirements_rejects_missing_section():
    with pytest.raises(ValueError, match="METHOD_SIGNATURE"):
        validate_requirements(
            VALID_REQUIREMENTS.replace("=== METHOD_SIGNATURE ===", "")
        )


def test_validate_requirements_rejects_multiple_methods():
    second_signature = (
        "\nmethod Minimum(a: Nat, b: Nat) returns (result: Nat)"
    )
    multi_method = VALID_REQUIREMENTS.replace(
        "\n\n=== TEST_CASES ===",
        second_signature + "\n\n=== TEST_CASES ===",
    )

    with pytest.raises(ValueError, match="exactly one method signature; found 2"):
        validate_requirements(multi_method)


def test_prepare_parser_targets_text_without_a_lean_project():
    args = _parser().parse_args(
        [
            "Return the larger number",
            "--output-file",
            "max_spec.txt",
            "--provider",
            "openai",
            "--model",
            "test-model",
        ]
    )

    assert args.output_file == "max_spec.txt"
    assert not hasattr(args, "project")
    assert REQUIRED_SECTIONS == (
        "=== TASK_DESCRIPTION ===",
        "=== METHOD_SIGNATURE ===",
        "=== TEST_CASES ===",
    )


@pytest.mark.asyncio
async def test_expand_requirements_returns_legacy_pipeline_format(monkeypatch):
    class FakeLLM:
        async def ainvoke(self, _messages):
            return AIMessage(content=VALID_REQUIREMENTS)

    monkeypatch.setattr(prepare, "get_llm", lambda *_args: FakeLLM())
    monkeypatch.setattr(prepare, "check_limits_before_llm_call", lambda: None)
    monkeypatch.setattr(prepare, "set_current_agent", lambda _name: None)
    monkeypatch.setattr(
        prepare,
        "log_llm_interaction",
        lambda _agent, _messages, _response: None,
    )

    result = await prepare.expand_requirements(
        "Return the larger number",
        TEST_CONFIG,
    )

    assert result == VALID_REQUIREMENTS
    assert "import Velvet" not in result


@pytest.mark.asyncio
async def test_expand_requirements_rejects_wrong_format(monkeypatch):
    class FakeLLM:
        async def ainvoke(self, _messages):
            return AIMessage(content="Title\nWrong format")

    monkeypatch.setattr(prepare, "get_llm", lambda *_args: FakeLLM())
    monkeypatch.setattr(prepare, "check_limits_before_llm_call", lambda: None)
    monkeypatch.setattr(prepare, "set_current_agent", lambda _name: None)
    monkeypatch.setattr(
        prepare,
        "log_llm_interaction",
        lambda _agent, _messages, _response: None,
    )

    with pytest.raises(ValueError, match="TASK_DESCRIPTION"):
        await prepare.expand_requirements(
            "Return the larger number",
            TEST_CONFIG,
        )


@pytest.mark.asyncio
async def test_revise_requirements_includes_draft_and_feedback(monkeypatch):
    recorded_messages = []

    class FakeLLM:
        async def ainvoke(self, messages):
            recorded_messages.extend(messages)
            return AIMessage(content=REVISED_REQUIREMENTS)

    monkeypatch.setattr(prepare, "get_llm", lambda *_args: FakeLLM())
    monkeypatch.setattr(prepare, "check_limits_before_llm_call", lambda: None)
    monkeypatch.setattr(prepare, "set_current_agent", lambda _name: None)
    monkeypatch.setattr(
        prepare,
        "log_llm_interaction",
        lambda _agent, _messages, _response: None,
    )

    result = await prepare.revise_requirements(
        "Return the larger number",
        VALID_REQUIREMENTS,
        "Require both inputs to be positive.",
        TEST_CONFIG,
    )

    assert result == REVISED_REQUIREMENTS
    user_prompt = str(recorded_messages[-1].content)
    assert VALID_REQUIREMENTS in user_prompt
    assert "Require both inputs to be positive." in user_prompt


@pytest.mark.asyncio
async def test_review_app_saves_valid_requirements(tmp_path: Path):
    app = RequirementsReviewApp(
        VALID_REQUIREMENTS,
        tmp_path / "maximum.txt",
        "Return the larger number",
        TEST_CONFIG,
    )

    async with app.run_test() as pilot:
        await pilot.press("ctrl+s")

    assert app.return_value == VALID_REQUIREMENTS


@pytest.mark.asyncio
async def test_review_app_can_cancel(tmp_path: Path):
    app = RequirementsReviewApp(
        VALID_REQUIREMENTS,
        tmp_path / "maximum.txt",
        "Return the larger number",
        TEST_CONFIG,
    )

    async with app.run_test() as pilot:
        await pilot.press("escape")

    assert app.return_value is None


@pytest.mark.asyncio
async def test_review_app_revises_without_exiting(
    monkeypatch, tmp_path: Path
):
    feedback_seen = []

    async def fake_revise(description, current_draft, feedback, config):
        feedback_seen.append((description, current_draft, feedback, config))
        return REVISED_REQUIREMENTS

    monkeypatch.setattr(prepare, "revise_requirements", fake_revise)
    app = RequirementsReviewApp(
        VALID_REQUIREMENTS,
        tmp_path / "maximum.txt",
        "Return the larger number",
        TEST_CONFIG,
    )

    async with app.run_test() as pilot:
        await pilot.press("ctrl+r")
        feedback_editor = app.screen.query_one("#revision-feedback", prepare.TextArea)
        feedback_editor.text = "Require both inputs to be positive."
        await pilot.press("ctrl+enter")
        await app.workers.wait_for_complete()

        editor = app.query_one("#requirements-editor", prepare.TextArea)
        assert editor.text == REVISED_REQUIREMENTS
        assert app.return_value is None
        await pilot.press("ctrl+s")

    assert feedback_seen == [
        (
            "Return the larger number",
            VALID_REQUIREMENTS,
            "Require both inputs to be positive.",
            TEST_CONFIG,
        )
    ]
    assert app.return_value == REVISED_REQUIREMENTS


@pytest.mark.asyncio
async def test_escape_closes_feedback_dialog_only(tmp_path: Path):
    app = RequirementsReviewApp(
        VALID_REQUIREMENTS,
        tmp_path / "maximum.txt",
        "Return the larger number",
        TEST_CONFIG,
    )

    async with app.run_test() as pilot:
        await pilot.press("ctrl+r")
        await pilot.press("escape")

        assert app.query_one("#requirements-editor", prepare.TextArea)
        assert app.return_value is None
        await pilot.press("ctrl+s")

    assert app.return_value == VALID_REQUIREMENTS
