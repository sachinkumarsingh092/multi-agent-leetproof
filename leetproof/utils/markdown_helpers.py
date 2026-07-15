"""Helper functions for parsing markdown content.

This module provides utilities for extracting semantic sections from markdown text,
useful for breaking down informal reasoning into searchable chunks.
"""

import re
from typing import List

import mistune

from logging_config import get_logger

logger = get_logger(__name__)


def _extract_text_from_token(token: dict) -> str:
    """Recursively extract all text from a mistune token tree.

    Args:
        token: A mistune AST token dictionary

    Returns:
        Extracted text content from the token and its children
    """
    token_type = token.get("type", "")

    # Direct text node
    if token_type == "text":
        return token.get("raw", "")

    # Code block - include the code
    if token_type == "block_code" or token_type == "codespan":
        return token.get("raw", "")

    # Recursively gather text from children
    children = token.get("children", [])
    if isinstance(children, list):
        parts = []
        for child in children:
            if isinstance(child, dict):
                text = _extract_text_from_token(child)
                if text.strip():
                    parts.append(text.strip())
        return " ".join(parts)

    return ""


def split_markdown_into_sections(
    markdown_text: str, min_section_length: int = 20
) -> List[str]:
    """Split markdown text into semantic sections based on structure.

    Uses mistune to parse markdown and extract logical sections from:
    - Numbered lists (1. 2. 3.)
    - Bullet lists (- or *)
    - Headers (#, ##, ###)
    - Paragraphs

    Each section is a coherent semantic unit suitable for search queries.

    Args:
        markdown_text: The markdown text to split
        min_section_length: Minimum character length for a section (default: 20)

    Returns:
        List of text sections extracted from the markdown
    """
    sections = []

    try:
        # Parse markdown into AST
        md = mistune.create_markdown(renderer=None)
        tokens = md(markdown_text)

        current_section = []

        for token in tokens:
            if not isinstance(token, dict):
                continue

            token_type = token.get("type", "")

            if token_type == "heading":
                # Start new section on heading
                if current_section:
                    sections.append("\n".join(current_section))
                    current_section = []
                # Add heading text
                children = token.get("children", [])
                text = "".join(
                    c.get("raw", "")
                    for c in children
                    if isinstance(c, dict) and c.get("type") == "text"
                )
                current_section.append(text)

            elif token_type == "list":
                # Each list item becomes a section
                if current_section:
                    sections.append("\n".join(current_section))
                    current_section = []

                for item in token.get("children", []):
                    if isinstance(item, dict):
                        item_text = _extract_text_from_token(item)
                        if item_text.strip():
                            sections.append(item_text.strip())

            elif token_type == "paragraph":
                text = _extract_text_from_token(token)
                if text.strip():
                    current_section.append(text.strip())

            elif token_type == "block_code":
                # Include code blocks in current section
                code = token.get("raw", "")
                if code.strip():
                    current_section.append(code.strip())

        # Don't forget the last section
        if current_section:
            sections.append("\n".join(current_section))

    except Exception as e:
        logger.debug(f"Markdown parsing failed, falling back to paragraph split: {e}")
        # Fallback: split by double newlines
        paragraphs = re.split(r"\n\s*\n", markdown_text)
        sections = [p.strip() for p in paragraphs if p.strip()]

    # Filter out very short sections and ensure we have at least one
    sections = [s for s in sections if len(s) >= min_section_length]
    if not sections:
        sections = [markdown_text]

    return sections
