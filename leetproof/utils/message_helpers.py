"""Helpers for managing message history and reducing token usage."""

import json
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import List, Sequence, Optional, Dict, Any
from langchain_core.messages import (
    BaseMessage,
    HumanMessage,
    AIMessage,
    SystemMessage,
    ToolMessage,
)
from config.constants import SESSIONS_DIR
from logging_config import get_logger

logger = get_logger(__name__)

# Global counter for tracking LLM interactions
_interaction_counter = 0

# Global session name for saving logs (set at startup)
_session_name: Optional[str] = None


def init_message_helpers(session_name: Optional[str] = None) -> None:
    """Initialize message helpers with session name for log saving.

    Args:
        session_name: Session name for saving LLM logs
    """
    global _session_name
    _session_name = session_name


def add_messages_with_deduplication(
    left: Sequence[BaseMessage], right: Sequence[BaseMessage]
) -> List[BaseMessage]:
    """
    Custom message reducer that aggressively removes old conversation to save tokens.

    Strategy:
    - When a new HumanMessage arrives (retry), remove ALL previous HumanMessages
    - Also remove ALL associated AIMessages and ToolMessages from the old conversation
    - ONLY keep SystemMessages (contains prompts, documentation, etc.)
    - If right is explicitly empty list with no messages, CLEAR ALL (used by judge on FAIL)

    This is based on the insight that on retry:
    - The new HumanMessage contains all necessary context
    - Old conversation history (Human/AI/Tool exchanges) is redundant
    - Only the SystemMessage (agent instructions + docs) needs to persist

    Keeps:
    - SystemMessages (agent instructions, documentation - needed every time)

    Removes on retry:
    - Old HumanMessages (redundant with new retry message)
    - Old AIMessages (redundant, new conversation will generate new ones)
    - Old ToolMessages (redundant, new conversation can re-fetch if needed)

    Args:
        left: Existing messages
        right: New messages to add

    Returns:
        Combined message list with aggressive deduplication applied

    Example:
        Before: [SystemMessage, HumanMessage1, AIMessage1, ToolMessage1, ToolMessage2]
        New: [HumanMessage2]
        After: [SystemMessage, HumanMessage2]
        Token savings: Removed 4 messages (potentially 10K+ tokens)
    """
    # Special case: if right is explicitly empty AND left has messages, this is an explicit clear request
    if isinstance(right, list) and len(right) == 0 and len(left) > 0:
        logger.info(
            f"Explicit message clear requested - removing all {len(left)} messages"
        )
        return []

    # Check if right contains a HumanMessage (indicates a retry)
    has_new_human_message = any(isinstance(msg, HumanMessage) for msg in right)

    if has_new_human_message:
        # AGGRESSIVE PRUNING: Keep ONLY SystemMessages from left
        # Remove ALL HumanMessages, AIMessages, and ToolMessages
        original_count = len(left)
        filtered_left = [msg for msg in left if isinstance(msg, SystemMessage)]
        removed = original_count - len(filtered_left)

        if removed > 0:
            # Calculate breakdown for logging
            removed_human = sum(1 for msg in left if isinstance(msg, HumanMessage))
            removed_ai = sum(1 for msg in left if isinstance(msg, AIMessage))
            removed_tool = sum(1 for msg in left if isinstance(msg, ToolMessage))

            logger.info(
                f"Token optimization: Removed {removed} messages on retry "
                f"(Human: {removed_human}, AI: {removed_ai}, Tool: {removed_tool}). "
                f"Kept {len(filtered_left)} SystemMessages"
            )

        # Return only SystemMessages + new messages
        return list(filtered_left) + list(right)
    else:
        # No new HumanMessage, just append normally
        return list(left) + list(right)


class PromptSegment(str, Enum):
    """Prompt segment kind used for provider-aware materialization."""

    STABLE = "stable"
    DYNAMIC = "dynamic"


@dataclass(frozen=True)
class PromptFragment:
    """Typed prompt fragment tagged with a segment kind."""

    text: str
    segment: PromptSegment


@dataclass(frozen=True)
class PromptSection:
    """A titled section in a structured prompt."""

    title: str
    content: PromptFragment


@dataclass(frozen=True)
class PromptSpec:
    """Typed prompt specification used by agents."""

    task: PromptFragment
    sections: tuple[PromptSection, ...] = ()
    instructions: PromptFragment | None = None
    closing: PromptFragment | None = None


@dataclass(frozen=True)
class PromptParts:
    """Rendered prompt split into stable and dynamic segments."""

    stable: str = ""
    dynamic: str = ""

    def full_text(self) -> str:
        if self.stable and self.dynamic:
            return f"{self.stable}\n\n{self.dynamic}"
        return self.stable or self.dynamic


def stable(text: str) -> PromptFragment:
    """Create a stable prompt fragment."""
    return PromptFragment(text=text, segment=PromptSegment.STABLE)


def dynamic(text: str) -> PromptFragment:
    """Create a dynamic prompt fragment."""
    return PromptFragment(text=text, segment=PromptSegment.DYNAMIC)


def section(title: str, content: PromptFragment) -> PromptSection:
    """Create a typed prompt section."""
    return PromptSection(title=title, content=content)


def bullets(lines: list[str], *, segment: PromptSegment) -> PromptFragment:
    """Create a bullet-list fragment."""
    body = "**INSTRUCTIONS:**\n" + "\n".join(f"- {line}" for line in lines)
    return PromptFragment(text=body, segment=segment)


def create_prompt(
    *,
    task: PromptFragment,
    sections: tuple[PromptSection, ...] = (),
    instructions: PromptFragment | None = None,
    closing: PromptFragment | None = None,
) -> PromptSpec:
    """Create a typed prompt specification."""
    return PromptSpec(
        task=task,
        sections=sections,
        instructions=instructions,
        closing=closing,
    )


def _render_segment(
    *,
    task: str | None,
    sections: tuple[PromptSection, ...],
    instructions: PromptFragment | None,
    closing: PromptFragment | None,
) -> str:
    """Render one prompt segment."""
    parts: list[str] = []
    if task:
        parts.append(task)
    for sec in sections:
        if sec.content.text:
            parts.append(f"**{sec.title}:**\n{sec.content.text}")
    if instructions and instructions.text:
        parts.append(instructions.text)
    if closing and closing.text:
        parts.append(f"**Remember:** {closing.text}")
    return "\n\n".join(parts)


def render_prompt(spec: PromptSpec) -> PromptParts:
    """Render a prompt spec into stable and dynamic text segments."""
    stable_sections = tuple(
        sec for sec in spec.sections if sec.content.segment == PromptSegment.STABLE
    )
    dynamic_sections = tuple(
        sec for sec in spec.sections if sec.content.segment == PromptSegment.DYNAMIC
    )

    stable_text = ""
    if spec.task.segment == PromptSegment.STABLE:
        stable_text = _render_segment(
            task=spec.task.text,
            sections=stable_sections,
            instructions=(
                spec.instructions
                if spec.instructions and spec.instructions.segment == PromptSegment.STABLE
                else None
            ),
            closing=(
                spec.closing
                if spec.closing and spec.closing.segment == PromptSegment.STABLE
                else None
            ),
        )

    dynamic_task = spec.task.text if spec.task.segment == PromptSegment.DYNAMIC else None
    dynamic_text = ""
    if (
        dynamic_task
        or dynamic_sections
        or (spec.instructions and spec.instructions.segment == PromptSegment.DYNAMIC)
        or (spec.closing and spec.closing.segment == PromptSegment.DYNAMIC)
    ):
        dynamic_text = _render_segment(
            task=dynamic_task,
            sections=dynamic_sections,
            instructions=(
                spec.instructions
                if spec.instructions and spec.instructions.segment == PromptSegment.DYNAMIC
                else None
            ),
            closing=(
                spec.closing
                if spec.closing and spec.closing.segment == PromptSegment.DYNAMIC
                else None
            ),
        )

    return PromptParts(stable=stable_text, dynamic=dynamic_text)


def code_block(content: str, language: str = "") -> str:
    """Wrap content in a fenced code block."""
    fence = f"```{language}" if language else "```"
    return f"{fence}\n{content}\n```"


def lean_block(content: str) -> str:
    """Wrap Lean code in a fenced code block."""
    return code_block(content, "lean")


def _flatten_leaves(obj, prefix: str = "") -> List[str]:
    """Recursively collect only leaf values as bold dotted-key + code snippet."""
    parts: List[str] = []
    if isinstance(obj, dict):
        for k, v in obj.items():
            key_path = f"{prefix}.{k}" if prefix else k
            if isinstance(v, (dict, list)):
                parts.extend(_flatten_leaves(v, key_path))
            else:
                parts.append(f"**{key_path}**\n\n```\n{v}\n```")
    elif isinstance(obj, list):
        for i, item in enumerate(obj):
            key_path = f"{prefix}[{i}]" if prefix else f"[{i}]"
            if isinstance(item, (dict, list)):
                parts.extend(_flatten_leaves(item, key_path))
            else:
                parts.append(f"**{key_path}**\n\n```\n{item}\n```")
    return parts


def _format_content_for_md(content) -> str:
    """Format message content for markdown logs, flattening nested structures.

    Only leaf values are rendered, each with a bold dotted-key path
    followed by the value in a code snippet.
    """
    if isinstance(content, str):
        return content
    if isinstance(content, (dict, list)):
        parts = _flatten_leaves(content)
        if parts:
            return "\n\n".join(parts)
    return str(content)


def log_llm_interaction(
    agent_name: str, messages: List[BaseMessage], response: BaseMessage
) -> None:
    """Log full LLM interaction (messages + response) to session.

    Saves in both markdown (readable) and JSON (structured) formats.

    Args:
        agent_name: Name of the agent
        messages: Input messages (system + human)
        response: LLM response
    """
    global _interaction_counter
    _interaction_counter += 1
    interaction_id = _interaction_counter

    try:
        if _session_name is None:
            logger.debug("Session name not initialized, skipping LLM interaction log")
            return

        session_dir = Path(SESSIONS_DIR) / _session_name / "llm_logs"
        agent_dir = session_dir / agent_name
        json_dir = agent_dir / "json-response"
        md_dir = agent_dir / "md-response"
        json_dir.mkdir(parents=True, exist_ok=True)
        md_dir.mkdir(parents=True, exist_ok=True)

        filename_base = f"{interaction_id:03d}"

        # Save JSON format — preserve raw content (may be str or list of blocks)
        json_data = {
            "interaction_id": interaction_id,
            "agent": agent_name,
            "messages": [
                {
                    "type": msg.__class__.__name__,
                    "content": msg.content,
                }
                for msg in messages
            ],
            "response": {
                "type": response.__class__.__name__,
                "content": response.content,
                "tool_calls": getattr(response, "tool_calls", None),
            },
        }
        json_file = json_dir / f"{filename_base}.json"
        with open(json_file, "w") as f:
            json.dump(json_data, f, indent=2, default=str)

        # Save markdown format
        md_lines = [
            f"# LLM Interaction #{interaction_id}",
            f"**Agent:** {agent_name}",
            "",
            "---",
            "",
            "## Input Messages",
            "",
        ]

        for i, msg in enumerate(messages):
            msg_type = msg.__class__.__name__
            content = _format_content_for_md(msg.content)
            md_lines.append(f"### [{i + 1}] {msg_type}")
            md_lines.append("")
            md_lines.append(content)
            md_lines.append("")

        md_lines.extend(
            [
                "---",
                "",
                "## Response",
                "",
                f"**Type:** {response.__class__.__name__}",
                "",
            ]
        )

        response_content = _format_content_for_md(response.content)
        md_lines.append(response_content)

        if hasattr(response, "tool_calls") and response.tool_calls:
            md_lines.extend(
                [
                    "",
                    "### Tool Calls",
                    "",
                    "```json",
                    json.dumps(response.tool_calls, indent=2, default=str),
                    "```",
                ]
            )

        md_file = md_dir / f"{filename_base}.md"
        md_file.write_text("\n".join(md_lines))

        logger.info(f"LLM interaction logged to: {json_file} and {md_file}")

    except (IOError, OSError, ValueError) as e:
        logger.warning(f"Failed to log LLM interaction: {e}")
