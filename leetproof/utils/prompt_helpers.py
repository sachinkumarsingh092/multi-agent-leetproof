"""Helper functions for loading agent system prompts."""

import os
from pathlib import Path
from typing import List, Optional
import importlib.resources
from logging_config import get_logger
from utils.message_helpers import create_prompt, render_prompt, section, stable

logger = get_logger(__name__)

# Base directory: use LLOOM_BASE_DIR (set by PyInstaller runtime hook) or __file__
_BASE = Path(os.environ.get('LLOOM_BASE_DIR', Path(__file__).parent.parent))

# Base directory for prompts
_PROMPTS_DIR = _BASE / "prompts"

# Base directory for the project root (for resolving relative paths)
_PROJECT_ROOT = _BASE


def _read_prompt_file(filename: str) -> Optional[str]:
    """Read a file from the prompts package, handling both dev and installed scenarios.

    Args:
        filename: Name of the file in prompts/ directory

    Returns:
        File content as string, or None if not found
    """
    # First try direct path (works in dev and most installed scenarios)
    direct_path = _PROMPTS_DIR / filename
    if direct_path.exists():
        try:
            # Resolve symlinks for dev environment
            resolved = direct_path.resolve()
            return resolved.read_text()
        except OSError:
            return direct_path.read_text()

    # Fallback: use importlib.resources for installed package
    try:
        # Python 3.9+ API
        files = importlib.resources.files("prompts")
        resource = files.joinpath(filename)
        return resource.read_text()
    except (TypeError, FileNotFoundError, AttributeError) as e:
        logger.debug(f"importlib.resources fallback failed for {filename}: {e}")
        return None


def load_system_prompt(
    prompt_filename: str, default_prompt: str = "You are an AI assistant."
) -> str:
    """Load system prompt from a markdown file, skipping YAML frontmatter.

    Args:
        prompt_filename: Name of the prompt file (e.g., "velvet-programmer.md")
        default_prompt: Fallback prompt if file not found

    Returns:
        The system prompt content (without YAML frontmatter)
    """
    content = _read_prompt_file(prompt_filename)

    if content is None:
        logger.warning(f"System prompt not found: {prompt_filename}, using default")
        return default_prompt

    # Skip YAML frontmatter if present (content between --- markers)
    if content.startswith("---"):
        parts = content.split("---", 2)
        if len(parts) >= 3:
            return parts[2].strip()

    return content


def load_additional_context_files(file_paths: List[str]) -> Optional[str]:
    """Load and concatenate additional context files for an agent.

    This function supports two path resolution strategies:
    1. Paths starting with "prompts/" are loaded from the prompts package
       (works both in dev with symlinks and when installed as a package)
    2. Other paths are resolved relative to the project root (dev only)

    Uses create_prompt helper for consistent formatting.

    Args:
        file_paths: List of file paths to load. Paths can be:
                   - In prompts/ (e.g., "prompts/velvet_documentation.md")
                   - Relative to project root

    Returns:
        Formatted context string using create_prompt, or None if no files loaded

    Example:
        >>> context = load_additional_context_files([
        ...     "prompts/velvet_documentation.md"
        ... ])
    """
    if not file_paths:
        return None

    context_sections = {}

    for file_path in file_paths:
        content = None

        if file_path.startswith("prompts/"):
            # Load from prompts package (handles both dev symlinks and installed package)
            filename = file_path[8:]  # Strip "prompts/" prefix
            content = _read_prompt_file(filename)
            if content is None:
                logger.warning(
                    f"Additional context file not found in prompts: {filename}"
                )
        else:
            # Resolve relative to project root (dev environment only)
            resolved_path = _PROJECT_ROOT / file_path
            try:
                resolved_path = resolved_path.resolve()
            except OSError:
                pass

            if resolved_path.exists():
                try:
                    content = resolved_path.read_text()
                except Exception as e:
                    logger.error(f"Failed to read {file_path}: {e}")
            else:
                logger.warning(f"Additional context file not found: {file_path}")

        if content:
            # Use filename as section name
            section_name = Path(file_path).stem.replace("_", " ").title()
            context_sections[section_name] = content
            logger.info(
                f"Loaded additional context from {file_path} ({len(content)} chars)"
            )

    if not context_sections:
        return None

    return render_prompt(
        create_prompt(
            task=stable("The following additional context/documentation is provided for reference:"),
            sections=tuple(section(k, stable(v)) for k, v in context_sections.items()),
        )
    ).full_text()
