"""LeanExplore semantic search tool for agents."""

from langchain_core.tools import tool

from logging_config import get_logger
from utils.lean_explore_service import (
    semantic_search,
    format_results_for_prompt,
)

logger = get_logger(__name__)


@tool
async def lean_explore_search(query: str, num_results: int = 5) -> str:
    """Search for Lean functions, theorems, and lemmas using semantic search.

    Searches through Mathlib and standard library using natural language queries.
    Returns declarations with their full type signatures and documentation.

    **Query types that work well:**
    - Describe what a function does: "check if all elements satisfy predicate"
    - Describe the type signature: "Array to List conversion"
    - Describe a property: "fold over array with boolean and"
    - Name patterns: "Array.all", "List.foldl"

    **Example queries:**
    - "array all elements satisfy predicate" → finds Array.all, Array.any
    - "fold left over array" → finds Array.foldl
    - "list to array" → finds List.toArray, Array.toList
    - "boolean and equals true" → finds Bool.and_eq_true
    - "array size" → finds Array.size
    - "get element at index" → finds Array.get, Array.getElem

    **Tips for good queries:**
    - Be specific about the data structure (Array, List, etc.)
    - Describe the operation you want to perform
    - Include relevant types if known

    Args:
        query: Natural language description of what you're looking for
        num_results: Number of results to return (default: 5)

    Returns:
        Formatted list of Lean declarations with names, type signatures, and docs
    """
    try:
        results = await semantic_search(
            query=query,
            num_results=num_results,
            verify=False,  # Skip verification for speed
        )

        if not results:
            return "No results found. Try a different query."

        return format_results_for_prompt(results, max_results=num_results)

    except Exception as e:
        logger.error(f"LeanExplore search failed: {e}")
        return f"Search failed: {e}"
