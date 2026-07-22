"""Formalize reviewed natural-language specifications as Lean/Velvet contracts."""

from __future__ import annotations

import os
import re
from dataclasses import dataclass
from pathlib import Path

from langchain_core.messages import AIMessage, BaseMessage, HumanMessage, SystemMessage

from logging_config import get_logger
from providers import LLMConfig, ReasoningLevel, get_llm
from utils.lean.parser import LeanFile, _remove_comments, parse_test_cases
from utils.message_helpers import log_llm_interaction
from utils.token_tracker import check_limits_before_llm_call, set_current_agent

logger = get_logger(__name__)

REQUIRED_IMPORTS = (
    "Velvet.Std",
    "Extensions.Tactics",
    "Extensions.SpecDSL",
    "Extensions.VelvetPBT",
    "Mathlib.Tactic",
)
REQUIRED_OPTIONS = (
    "set_option maxHeartbeats 10000000",
    "set_option pp.coercions false",
    "set_option pp.funBinderTypes true",
    'set_option loom.semantics.termination "total"',
    'set_option loom.semantics.choice "demonic"',
)
REQUIRED_SECTIONS = ("Specs", "Impl", "TestCases")
MAX_GENERATION_ATTEMPTS = 3
PROMPT_PATH = Path(__file__).parent / "prompts" / "FormalizeContract.md"


class FormalizationError(RuntimeError):
    """Raised when reviewed text cannot be formalized as a valid contract."""


@dataclass(frozen=True)
class ContractValidation:
    """Structural validation result for a generated formal contract."""

    errors: tuple[str, ...]
    method_name: str | None = None

    @property
    def valid(self) -> bool:
        return not self.errors


def _get_velvet_method(content: str):
    """Load the Velvet parser only when validating generated content."""
    from utils.velvet_helpers import get_velvet_method

    return get_velvet_method(content)


def _typecheck_contract(file_path: str):
    """Load the Lean build stack only when a candidate is ready."""
    from tools.lean_build import lean_build_file_helper

    return lean_build_file_helper(file_path)


def extract_lean_code(response_text: str) -> str:
    """Extract a Lean file from a plain or fenced LLM response."""
    lean_fence = re.search(
        r"```(?:lean4?|Lean)\s*\n(.*?)```", response_text, re.DOTALL
    )
    if lean_fence:
        return lean_fence.group(1).strip() + "\n"

    generic_fence = re.search(r"```\s*\n(.*?)```", response_text, re.DOTALL)
    if generic_fence:
        return generic_fence.group(1).strip() + "\n"

    return response_text.strip() + "\n"


def _extract_response_text(response: AIMessage) -> str:
    content = response.content
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts: list[str] = []
        for block in content:
            if isinstance(block, str):
                parts.append(block)
            elif isinstance(block, dict) and block.get("type") == "text":
                parts.append(str(block.get("text", "")))
        return "\n".join(parts)
    return str(content or "")


def validate_contract(content: str) -> ContractValidation:
    """Validate the formal-contract shape expected by code generation."""
    errors: list[str] = []
    clean = _remove_comments(content)

    imports = tuple(re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", clean))
    if imports != REQUIRED_IMPORTS:
        errors.append(
            "Imports must be exactly, in order: " + ", ".join(REQUIRED_IMPORTS)
        )

    forbidden_patterns = {
        "axiom": r"\baxiom\b",
        "admit": r"\badmit\b",
        "unsafe": r"\bunsafe\b",
        "partial": r"\bpartial\b",
        "custom syntax or elaborators": r"\b(?:elab|macro|syntax|initialize|run_tac)\b",
        "evaluation commands": r"(?m)^\s*#(?:eval|check|print|reduce|compile)\b",
    }
    for label, pattern in forbidden_patterns.items():
        if re.search(pattern, clean):
            errors.append(f"Contract must not contain {label}")

    sorry_count = len(re.findall(r"\bsorry\b", clean))
    if sorry_count != 1:
        errors.append(
            f"Contract must contain exactly one sorry in prove_correct; found {sorry_count}"
        )

    try:
        lean_file = LeanFile.from_content(content)
    except Exception as exc:
        errors.append(f"Could not parse Lean sections: {exc}")
        return ContractValidation(tuple(errors))

    if tuple(lean_file.section_names()) != REQUIRED_SECTIONS:
        errors.append(
            "Sections must be exactly, in order: " + ", ".join(REQUIRED_SECTIONS)
        )

    prologue = _remove_comments(lean_file.prologue)
    unexpected_prologue = [
        line
        for line in prologue.splitlines()
        if line.strip()
        and not line.lstrip().startswith(("import ", "set_option "))
    ]
    if unexpected_prologue:
        errors.append("Only imports, set_option commands, and comments may precede Specs")

    options = tuple(
        line.strip()
        for line in clean.splitlines()
        if line.lstrip().startswith("set_option ")
    )
    if options != REQUIRED_OPTIONS:
        errors.append(
            "set_option commands must be exactly, in order: "
            + ", ".join(REQUIRED_OPTIONS)
        )

    for section in lean_file.sections:
        if _remove_comments(section.trailing_content).strip():
            errors.append(f"Declarations are not allowed after section {section.name}")

    specs = lean_file.get_section("Specs")
    impl = lean_file.get_section("Impl")
    tests = lean_file.get_section("TestCases")
    if specs is None or impl is None or tests is None:
        return ContractValidation(tuple(errors))

    specs_clean = _remove_comments(specs.content)
    if not re.search(r"\bdef\s+precondition\b", specs_clean):
        errors.append("Specs must define precondition")
    if not re.search(r"\bdef\s+postcondition\b", specs_clean):
        errors.append("Specs must define postcondition")

    method_name: str | None = None
    try:
        method_count = len(re.findall(r"(?m)^\s*method\s+\S+", clean))
        if method_count != 1:
            errors.append(f"Contract must define exactly one method; found {method_count}")

        method = _get_velvet_method(impl.content)
        method_name = method.name
        if not any(
            re.match(r"^precondition\b", requirement.strip())
            for requirement in method.requires
        ):
            errors.append("The method must require precondition")
        if not any(
            re.match(r"^postcondition\b", condition.strip())
            for condition in method.ensures
        ):
            errors.append("The method must ensure postcondition")

        prove_pattern = (
            rf"\bprove_correct\s+{re.escape(method.name)}\s+by\s+sorry\b"
        )
        if not re.search(prove_pattern, _remove_comments(impl.content)):
            errors.append(
                f"Impl must end with 'prove_correct {method.name} by sorry'"
            )

        test_cases = parse_test_cases(tests.content, method)
        if not test_cases:
            errors.append("TestCases must define at least one test<N> case")
        for test_case in test_cases:
            missing_inputs = [
                param.name
                for param in method.params
                if param.name not in test_case.inputs
            ]
            if missing_inputs:
                errors.append(
                    f"{test_case.name} is missing inputs: {', '.join(missing_inputs)}"
                )
            if test_case.expected_return is None:
                errors.append(f"{test_case.name} is missing Expected")
            for param in method.params:
                if param.is_mut and param.name not in test_case.expected_mutations:
                    errors.append(
                        f"{test_case.name} is missing Expected_{param.name}"
                    )
    except Exception as exc:
        errors.append(f"Impl is not a valid Velvet method contract: {exc}")

    return ContractValidation(tuple(errors), method_name)


def _retry_prompt(
    reviewed_specification: str, previous_candidate: str, failure: str
) -> str:
    prompt = f"""Formalize this frozen, human-reviewed natural-language specification:

{reviewed_specification}
"""
    if previous_candidate:
        prompt += f"""
The previous candidate was invalid:

```lean
{previous_candidate}
```

Validation or build feedback:
{failure[:8000]}

Correct every reported issue without changing the reviewed requirements.
"""
    prompt += "\nReturn only the complete Lean file."
    return prompt


async def generate_contract(
    reviewed_specification: str,
    output_path: Path,
    project_root: Path,
    config: LLMConfig,
) -> str:
    """Generate, validate, type-check, and publish a formal contract."""
    system_prompt = PROMPT_PATH.read_text()
    llm = get_llm(config, ReasoningLevel.LOW)
    temp_path = output_path.with_name(
        f"{output_path.stem}_formalize_{os.getpid()}_tmp.lean"
    )
    previous_candidate = ""
    failure = ""

    try:
        for attempt in range(1, MAX_GENERATION_ATTEMPTS + 1):
            logger.info(
                "Formalizing reviewed specification (attempt %d/%d)",
                attempt,
                MAX_GENERATION_ATTEMPTS,
            )
            messages: list[BaseMessage] = [
                SystemMessage(content=system_prompt),
                HumanMessage(
                    content=_retry_prompt(
                        reviewed_specification, previous_candidate, failure
                    )
                ),
            ]
            check_limits_before_llm_call()
            set_current_agent("contract_formalizer")
            raw_response = await llm.ainvoke(messages)
            response = (
                raw_response
                if isinstance(raw_response, AIMessage)
                else AIMessage(content=str(raw_response))
            )
            log_llm_interaction("contract_formalizer", messages, response)
            candidate = extract_lean_code(_extract_response_text(response))
            validation = validate_contract(candidate)

            if not validation.valid:
                previous_candidate = candidate
                failure = "\n".join(f"- {error}" for error in validation.errors)
                logger.warning(
                    "Formal contract failed structural validation:\n%s", failure
                )
                continue

            temp_path.write_text(candidate)
            relative_temp = temp_path.relative_to(project_root)
            build = _typecheck_contract(str(relative_temp))
            if build.typechecks:
                os.replace(temp_path, output_path)
                logger.info("Formal contract passed validation and Lean type-checking")
                return candidate

            previous_candidate = candidate
            failure = build.as_string(["error"]) or build.build_log
            logger.warning("Formal contract failed Lean type-checking:\n%s", failure)
    finally:
        temp_path.unlink(missing_ok=True)

    raise FormalizationError(
        f"Could not formalize the reviewed specification after "
        f"{MAX_GENERATION_ATTEMPTS} attempts.\nLast failure:\n{failure}"
    )
