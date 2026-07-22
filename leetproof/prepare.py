"""Generate and review a structured pipeline input from a short description."""

from __future__ import annotations

import argparse
import asyncio
import re
import sys
from pathlib import Path

from langchain_core.messages import AIMessage, BaseMessage, HumanMessage, SystemMessage
from textual import work
from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.containers import Vertical
from textual.screen import ModalScreen
from textual.widgets import Footer, Header, Label, Static, TextArea

from providers import LLMConfig, ReasoningLevel, get_llm
from requirements import validate_requirements
from utils.message_helpers import log_llm_interaction
from utils.token_tracker import (
    check_limits_before_llm_call,
    init_token_tracker,
    set_current_agent,
)

PROMPT_PATH = Path(__file__).parent / "prompts" / "RequirementsGen.md"


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


def normalize_requirements_text(text: str) -> str:
    """Normalize a plain or fenced textual LLM response."""
    fenced = re.fullmatch(
        r"\s*```(?:text|txt|markdown|md)?\s*\n(.*?)```\s*",
        text,
        re.DOTALL | re.IGNORECASE,
    )
    if fenced:
        text = fenced.group(1)
    return text.strip()


async def expand_requirements(description: str, config: LLMConfig) -> str:
    """Generate a draft in the reviewed pipeline-input format."""
    llm = get_llm(config, ReasoningLevel.LOW)
    messages: list[BaseMessage] = [
        SystemMessage(content=PROMPT_PATH.read_text(encoding="utf-8")),
        HumanMessage(content=description),
    ]
    check_limits_before_llm_call()
    set_current_agent("requirements_generator")
    raw_response = await llm.ainvoke(messages)
    response = (
        raw_response
        if isinstance(raw_response, AIMessage)
        else AIMessage(content=str(raw_response))
    )
    log_llm_interaction("requirements_generator", messages, response)

    specification = normalize_requirements_text(_extract_response_text(response))
    validate_requirements(specification)
    return specification


async def revise_requirements(
    description: str,
    current_draft: str,
    feedback: str,
    config: LLMConfig,
) -> str:
    """Revise a requirements draft according to explicit reviewer feedback."""
    llm = get_llm(config, ReasoningLevel.LOW)
    messages: list[BaseMessage] = [
        SystemMessage(content=PROMPT_PATH.read_text(encoding="utf-8")),
        HumanMessage(
            content=f"""Original request:
{description}

Current requirements draft:
{current_draft}

Reviewer feedback:
{feedback}

Revise the complete draft to address the feedback. Preserve all requirements
that the reviewer did not ask to change. Return only the full three-section
pipeline input."""
        ),
    ]
    check_limits_before_llm_call()
    set_current_agent("requirements_reviser")
    raw_response = await llm.ainvoke(messages)
    response = (
        raw_response
        if isinstance(raw_response, AIMessage)
        else AIMessage(content=str(raw_response))
    )
    log_llm_interaction("requirements_reviser", messages, response)

    specification = normalize_requirements_text(_extract_response_text(response))
    validate_requirements(specification)
    return specification


class RevisionFeedbackScreen(ModalScreen[str | None]):
    """Collect revision instructions without leaving the review app."""

    BINDINGS = [
        Binding("ctrl+enter", "submit", "Submit revision", priority=True),
        Binding("f5", "submit", "Submit revision", priority=True),
        Binding("escape", "cancel", "Back", priority=True),
    ]

    CSS = """
    RevisionFeedbackScreen {
        align: center middle;
    }

    #revision-dialog {
        width: 80%;
        height: 60%;
        padding: 1 2;
        border: solid $accent;
        background: $surface;
    }

    #revision-feedback {
        height: 1fr;
        margin-top: 1;
    }
    """

    def compose(self) -> ComposeResult:
        with Vertical(id="revision-dialog"):
            yield Label(
                "Describe the changes for the model. "
                "Ctrl+Enter or F5 submits; Esc returns to the draft."
            )
            yield TextArea(id="revision-feedback")
            yield Footer()

    def on_mount(self) -> None:
        self.query_one("#revision-feedback", TextArea).focus()

    def action_submit(self) -> None:
        feedback = self.query_one("#revision-feedback", TextArea).text.strip()
        if not feedback:
            self.notify("Enter revision feedback first.", severity="warning")
            return
        self.dismiss(feedback)

    def action_cancel(self) -> None:
        self.dismiss(None)


class RequirementsReviewApp(App[str | None]):
    """Edit and approve generated requirements before saving."""

    BINDINGS = [
        Binding("ctrl+s", "save", "Save", priority=True),
        Binding("ctrl+r", "revise", "Revise with model", priority=True),
        Binding("escape", "cancel", "Cancel"),
    ]

    CSS = """
    #review-instructions {
        padding: 1 2;
    }

    #requirements-editor {
        height: 1fr;
        border: solid $accent;
    }
    """

    def __init__(
        self,
        text: str,
        output_path: Path,
        description: str,
        config: LLMConfig,
    ) -> None:
        super().__init__()
        self.requirements_text = text
        self.output_path = output_path
        self.description = description
        self.config = config
        self.revision_in_progress = False

    def compose(self) -> ComposeResult:
        yield Header()
        yield Static(
            f"Review {self.output_path} — Ctrl+R to revise, "
            "Ctrl+S to save, Esc to cancel",
            id="review-instructions",
        )
        yield TextArea(
            self.requirements_text,
            id="requirements-editor",
            show_line_numbers=True,
        )
        yield Footer()

    def on_mount(self) -> None:
        self.query_one("#requirements-editor", TextArea).focus()

    def action_save(self) -> None:
        if self.revision_in_progress:
            self.notify("Wait for the current revision to finish.", severity="warning")
            return
        text = self.query_one("#requirements-editor", TextArea).text.strip()
        try:
            validate_requirements(text)
        except ValueError as error:
            self.notify(str(error), severity="error")
            return
        self.exit(text)

    def action_revise(self) -> None:
        if self.revision_in_progress:
            self.notify("A revision is already in progress.", severity="warning")
            return
        self.push_screen(RevisionFeedbackScreen(), self._start_revision)

    def _start_revision(self, feedback: str | None) -> None:
        if feedback:
            self.revision_in_progress = True
            self._revise_draft(feedback)

    @work(exclusive=True, exit_on_error=False)
    async def _revise_draft(self, feedback: str) -> None:
        editor = self.query_one("#requirements-editor", TextArea)
        current_draft = editor.text.strip()
        editor.disabled = True
        self.notify("Revising requirements draft…")
        try:
            revised = await revise_requirements(
                self.description,
                current_draft,
                feedback,
                self.config,
            )
        except Exception as error:
            self.notify(f"Revision failed: {error}", severity="error")
            return
        finally:
            self.revision_in_progress = False
            editor.disabled = False

        self.requirements_text = revised
        editor.load_text(revised)
        editor.focus()
        self.notify("Draft revised. Review the changes before saving.")

    def action_cancel(self) -> None:
        self.exit(None)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="lloom-agent prepare",
        description="Turn a short description into a reviewable pipeline input file.",
    )
    parser.add_argument("description", help="Short natural-language requirement")
    parser.add_argument(
        "--output-file",
        "-o",
        required=True,
        help="Approved pipeline input path; must end in .txt",
    )
    parser.add_argument(
        "--provider",
        required=True,
        choices=("openai", "google", "anthropic"),
    )
    parser.add_argument("--model", required=True)
    return parser


def main() -> None:
    parser = _parser()
    args = parser.parse_args()
    description = args.description.strip()
    if not description:
        parser.error("description must not be empty")

    output_path = Path(args.output_file)
    if output_path.suffix.lower() != ".txt":
        parser.error("--output-file must end in .txt")

    config = LLMConfig(provider=args.provider, model=args.model)
    init_token_tracker(model_name=args.model)
    print("Generating requirements draft...")
    try:
        text = asyncio.run(
            expand_requirements(
                description,
                config,
            )
        )
    except ValueError as error:
        print(f"Error: {error}", file=sys.stderr)
        sys.exit(1)

    reviewed_text = RequirementsReviewApp(
        text,
        output_path,
        description,
        config,
    ).run()
    if reviewed_text is None:
        print("Cancelled; no file was written.")
        return

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(reviewed_text + "\n", encoding="utf-8")
    print(f"Saved approved requirements to {output_path}")


if __name__ == "__main__":
    main()
