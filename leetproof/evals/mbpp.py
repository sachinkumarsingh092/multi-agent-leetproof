#!/usr/bin/env python3
"""
MBPP dataset loader - gets problems from mbpp-san-velvet-228.

Usage:
    python3 scripts/mbpp.py 1
    python3 scripts/mbpp.py 25 --components task_description method_signature
    python3 scripts/mbpp.py 1 -c task_description test_cases -f text
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


def _evals_dir() -> Path:
    """Return the evals/ directory, handling PyInstaller bundles."""
    import os
    base = os.environ.get('LLOOM_BASE_DIR')
    if base:
        return Path(base) / "evals"
    return Path(__file__).parent


def load_dataset() -> Dict[int, Dict[str, Any]]:
    """Load MBPP dataset and return as {position: problem}."""
    dataset_file = _evals_dir() / "benchmarks" / "mbpp-san-velvet-228.json"

    if not dataset_file.exists():
        raise FileNotFoundError(f"Dataset not found at {dataset_file}")

    with open(dataset_file) as f:
        data = json.load(f)

    # Convert to indexed format (1-based position)
    # Sort by task_id numerically for consistent ordering
    sorted_tasks = sorted(data.items(), key=lambda x: int(x[0]))
    indexed = {i+1: task for i, (_, task) in enumerate(sorted_tasks)}

    return indexed


def load_dataset_by_mbpp_id() -> Dict[int, Dict[str, Any]]:
    """Load MBPP dataset and return as {mbpp_id: problem}.

    The mbpp_id is the original MBPP task_id (e.g., 2, 3, 7, 8, ..., 809).
    """
    dataset_file = _evals_dir() / "benchmarks" / "mbpp-san-velvet-228.json"

    if not dataset_file.exists():
        raise FileNotFoundError(f"Dataset not found at {dataset_file}")

    with open(dataset_file) as f:
        data = json.load(f)

    # Return with integer mbpp_id as key
    return {int(task_id): task for task_id, task in data.items()}


def get_mbpp_id_to_position_map() -> Dict[int, int]:
    """Get mapping from MBPP ID (task_id) to position (1-228).

    Returns:
        Dict mapping mbpp_id -> position
    """
    dataset_file = _evals_dir() / "benchmarks" / "mbpp-san-velvet-228.json"

    if not dataset_file.exists():
        raise FileNotFoundError(f"Dataset not found at {dataset_file}")

    with open(dataset_file) as f:
        data = json.load(f)

    # Sort by task_id numerically for consistent ordering
    sorted_task_ids = sorted(data.keys(), key=lambda x: int(x))

    # Map mbpp_id to 1-based position
    return {int(task_id): i+1 for i, task_id in enumerate(sorted_task_ids)}


def get_position_to_mbpp_id_map() -> Dict[int, int]:
    """Get mapping from position (1-228) to MBPP ID (task_id).

    Returns:
        Dict mapping position -> mbpp_id
    """
    mbpp_to_pos = get_mbpp_id_to_position_map()
    return {pos: mbpp_id for mbpp_id, pos in mbpp_to_pos.items()}


def mbpp_id_to_position(mbpp_id: int) -> Optional[int]:
    """Convert MBPP ID (task_id) to position (1-228).

    Args:
        mbpp_id: Original MBPP task_id (e.g., 807)

    Returns:
        Position (1-228) or None if mbpp_id not found
    """
    mapping = get_mbpp_id_to_position_map()
    return mapping.get(mbpp_id)


def position_to_mbpp_id(position: int) -> Optional[int]:
    """Convert position (1-228) to MBPP ID (task_id).

    Args:
        position: Position in sorted list (1-228)

    Returns:
        MBPP task_id or None if position not found
    """
    mapping = get_position_to_mbpp_id_map()
    return mapping.get(position)


def get_problem(number: int, use_mbpp_id: bool = False, components: Optional[List[str]] = None) -> Dict[str, Any]:
    """Load an MBPP problem, optionally filtering to specific components.

    Args:
        number: Problem number (position 1-228) or MBPP task ID
        use_mbpp_id: If True, interpret number as MBPP task ID
        components: Optional list of keys to include

    Returns:
        Problem data dict
    """
    if use_mbpp_id:
        dataset = load_dataset_by_mbpp_id()
    else:
        dataset = load_dataset()
    if number not in dataset:
        kind = "MBPP ID" if use_mbpp_id else "position"
        raise KeyError(f"{kind} {number} not found in MBPP dataset")
    data = dataset[number]
    if components:
        data = {k: v for k, v in data.items() if k in components}
    return data


def format_text(data: Dict[str, Any]) -> str:
    """Format a problem dict as human-readable text (same as CLI text output)."""
    parts = []
    for key, value in data.items():
        parts.append(f"=== {key.upper()} ===")
        if isinstance(value, (dict, list)):
            parts.append(json.dumps(value, indent=2))
        else:
            parts.append(str(value))
        parts.append("")
    return "\n".join(parts)


def main():
    parser = argparse.ArgumentParser(
        description="Get MBPP benchmark problems",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 evals/mbpp.py 1                    # By position (1-228)
  python3 evals/mbpp.py 807 --mbpp-id        # By MBPP task ID
  python3 evals/mbpp.py 25 -c task_description method_signature
  python3 evals/mbpp.py 1 -c task_description test_cases -f text
        """
    )

    parser.add_argument("number", type=int, help="Problem number (position 1-228, or MBPP ID with --mbpp-id)")
    parser.add_argument("--mbpp-id", action="store_true", help="Interpret number as MBPP task ID instead of position")
    parser.add_argument("-c", "--components", nargs="+", help="Specific components to extract")
    parser.add_argument("-f", "--format", choices=["json", "text"], default="json")

    args = parser.parse_args()

    try:
        data = get_problem(args.number, use_mbpp_id=args.mbpp_id, components=args.components)
    except (KeyError, Exception) as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    if args.format == "json":
        print(json.dumps(data, indent=2))
    else:
        print(format_text(data))

    return 0


if __name__ == "__main__":
    sys.exit(main())
