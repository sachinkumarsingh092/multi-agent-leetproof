"""Helper for loading agent-specific context to inject as SystemMessages."""
import json
from pathlib import Path
from typing import Optional, Dict
from logging_config import get_logger

logger = get_logger(__name__)

# Global cache for agent context
_agent_context_cache: Optional[Dict[str, str]] = None


def load_agent_context_map(agent_context_json: Optional[str] = None) -> Dict[str, str]:
    """
    Load agent context mapping from JSON string.

    Args:
        agent_context_json: JSON string mapping agent names to file paths
                           Example: '{"velvet_programmer": "path/to/docs.md"}'

    Returns:
        Dict mapping agent names to their loaded context content
        Returns empty dict if agent_context_json is None or invalid

    Example:
        >>> context_map = load_agent_context_map('{"velvet_programmer": "docs.md"}')
        >>> print(context_map["velvet_programmer"])
        "# Documentation content..."
    """
    global _agent_context_cache

    # Return cached version if already loaded
    if _agent_context_cache is not None:
        return _agent_context_cache

    if not agent_context_json:
        logger.debug("No agent context specified (--agent-context)")
        _agent_context_cache = {}
        return _agent_context_cache

    try:
        # Parse JSON mapping
        agent_to_file = json.loads(agent_context_json)
        logger.info(f"Loaded agent context mapping with {len(agent_to_file)} agents")

        # Load each file
        context_map = {}
        for agent_name, file_path in agent_to_file.items():
            path = Path(file_path)
            if not path.exists():
                logger.warning(f"Context file for agent '{agent_name}' not found: {file_path}")
                continue

            try:
                content = path.read_text()
                context_map[agent_name] = content
                logger.info(f"Loaded context for '{agent_name}' from {file_path} ({len(content)} chars)")
            except Exception as e:
                logger.error(f"Failed to read context file for '{agent_name}': {e}")

        _agent_context_cache = context_map
        return context_map

    except json.JSONDecodeError as e:
        logger.error(f"Failed to parse --agent-context JSON: {e}")
        _agent_context_cache = {}
        return _agent_context_cache
    except Exception as e:
        logger.error(f"Error loading agent context: {e}")
        _agent_context_cache = {}
        return _agent_context_cache


def init_agent_context(agent_context_json: Optional[str] = None) -> Dict[str, str]:
    """Initialize the agent context from JSON at startup.

    Must be called once at application startup before any agent execution.

    Args:
        agent_context_json: JSON string mapping agent names to file paths

    Returns:
        Dict mapping agent names to their loaded context content
    """
    return load_agent_context_map(agent_context_json)


def get_agent_context(agent_name: str) -> Optional[str]:
    """
    Get context for a specific agent.

    Requires init_agent_context() to be called at startup.

    Args:
        agent_name: Name of the agent (e.g. "velvet_programmer")

    Returns:
        Context content as string, or None if not found

    Example:
        >>> docs = get_agent_context("velvet_programmer")
        >>> if docs:
        ...     messages.append(SystemMessage(content=docs))
    """
    if _agent_context_cache is None:
        logger.debug("Agent context not initialized, returning None")
        return None

    return _agent_context_cache.get(agent_name)
