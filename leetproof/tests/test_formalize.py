from pathlib import Path

import pytest
from langchain_core.messages import AIMessage

import formalize
from formalize import REQUIRED_SECTIONS, extract_lean_code, validate_contract
from providers import LLMConfig
from utils.lean.types import LakeBuildResult


EXAMPLE_CONTRACT = (
    Path(__file__).parent / "fixtures" / "ShippingFeeSpec.lean"
)


def test_extract_lean_code_from_fence():
    response = "Here is the result:\n```lean\nsection Specs\nend Specs\n```\n"

    assert extract_lean_code(response) == "section Specs\nend Specs\n"


def test_validate_worker_example_contract():
    result = validate_contract(EXAMPLE_CONTRACT.read_text())

    assert result.valid, result.errors
    assert result.errors == ()
    assert result.method_name == "calculateShippingFee"
    assert REQUIRED_SECTIONS == ("Specs", "Impl", "TestCases")


def test_validate_contract_rejects_additional_sorry():
    content = EXAMPLE_CONTRACT.read_text().replace(
        "def freeShippingThreshold : Nat := 5000",
        "def freeShippingThreshold : Nat := by sorry",
    )

    result = validate_contract(content)

    assert not result.valid
    assert any("exactly one sorry" in error for error in result.errors)


def test_validate_contract_rejects_axiom():
    content = EXAMPLE_CONTRACT.read_text().replace(
        "section Specs",
        "section Specs\naxiom inventedFact : False",
    )

    result = validate_contract(content)

    assert not result.valid
    assert "Contract must not contain axiom" in result.errors


@pytest.mark.asyncio
async def test_generate_contract_retries_then_publishes_atomically(
    monkeypatch, tmp_path: Path
):
    valid_contract = EXAMPLE_CONTRACT.read_text()

    class FakeLLM:
        def __init__(self):
            self.responses = ["not Lean", valid_contract]
            self.messages = []

        async def ainvoke(self, messages):
            self.messages.append(messages)
            return AIMessage(content=self.responses.pop(0))

    fake_llm = FakeLLM()
    built_paths = []
    monkeypatch.setattr(formalize, "get_llm", lambda *_args: fake_llm)
    monkeypatch.setattr(formalize, "check_limits_before_llm_call", lambda: None)
    monkeypatch.setattr(formalize, "set_current_agent", lambda _name: None)
    monkeypatch.setattr(
        formalize,
        "log_llm_interaction",
        lambda _agent, _messages, _response: None,
    )

    def fake_build(path):
        built_paths.append(path)
        return LakeBuildResult(typechecks=True, diagnostics=[])

    monkeypatch.setattr(formalize, "_typecheck_contract", fake_build)
    output_path = tmp_path / "FormalContract.lean"

    contract = await formalize.generate_contract(
        "A frozen, reviewed shipping fee specification.",
        output_path,
        tmp_path,
        LLMConfig(provider="openai", model="test-model"),
    )

    assert contract == valid_contract
    assert output_path.read_text() == valid_contract
    assert len(fake_llm.messages) == 2
    assert len(built_paths) == 1
    assert not list(tmp_path.glob("*_formalize_*_tmp.lean"))
