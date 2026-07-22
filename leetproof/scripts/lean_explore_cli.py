#!/usr/bin/env python3
"""
CLI tool for LeanExplore semantic search.

Usage:
    # Show current toolchain info
    uv run scripts/lean_explore_cli.py --info

    # Search with a query string (auto-verifies results by default)
    uv run scripts/lean_explore_cli.py "commutativity of addition"

    # Search without verification (faster but may return non-existent theorems)
    uv run scripts/lean_explore_cli.py "digits of natural number" --no-verify

    # Search with specific toolchain version
    uv run scripts/lean_explore_cli.py "addition" --toolchain 0.4.0

    # Skip verification for faster results
    uv run scripts/lean_explore_cli.py "query" --no-verify

    # Search with query from file
    uv run scripts/lean_explore_cli.py --file query.txt

    # Limit results
    uv run scripts/lean_explore_cli.py "addition" --limit 5

    # JSON output
    uv run scripts/lean_explore_cli.py "addition" --json
"""

import argparse
import asyncio
import json
import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.lean_explore_service import semantic_search, format_results_for_prompt

try:
    from lean_explore import defaults as lean_defaults
except ImportError:
    lean_defaults = None  # type: ignore


def get_toolchain_info():
    """Get information about available and active toolchains."""
    if not lean_defaults:
        return None

    toolchains_dir = lean_defaults.LEAN_EXPLORE_TOOLCHAINS_BASE_DIR
    active_config = lean_defaults.ACTIVE_TOOLCHAIN_CONFIG_FILE_PATH

    info = {
        "default": lean_defaults.DEFAULT_ACTIVE_TOOLCHAIN_VERSION,
        "available": [],
        "active": None,
        "active_exists": False
    }

    # Get available toolchains
    if toolchains_dir.exists():
        info["available"] = sorted([d.name for d in toolchains_dir.iterdir() if d.is_dir()])

    # Get active toolchain
    if active_config.exists():
        info["active"] = active_config.read_text().strip()
        active_dir = toolchains_dir / info["active"]
        info["active_exists"] = active_dir.exists()
    else:
        info["active"] = info["default"]
        default_version = info["default"]
        if isinstance(default_version, str):
            info["active_exists"] = (toolchains_dir / default_version).exists()
        else:
            info["active_exists"] = False

    return info


def set_active_toolchain(version: str):
    """Set the active toolchain version."""
    if not lean_defaults:
        return False

    active_config = lean_defaults.ACTIVE_TOOLCHAIN_CONFIG_FILE_PATH
    active_config.parent.mkdir(parents=True, exist_ok=True)
    active_config.write_text(version)
    return True


def show_toolchain_info():
    """Display current toolchain information."""
    info = get_toolchain_info()
    if not info:
        print("Error: lean-xplore package not available", file=sys.stderr)
        return

    print("LeanExplore Toolchain Information")
    print("=" * 60)
    print(f"Default toolchain: {info['default']}")
    print(f"Active toolchain:  {info['active']}", end="")
    if info['active_exists']:
        print(" ✓")
    else:
        print(" ✗ (data not downloaded)")

    print(f"\nAvailable toolchains (downloaded):")
    if info['available']:
        for tc in info['available']:
            marker = " (active)" if tc == info['active'] else ""
            print(f"  - {tc}{marker}")
    else:
        print("  None")

    print("\nToolchain versions:")
    print("  0.2.0 → Mathlib v4.19.0 (May 2025)")
    print("  0.4.0 → Mathlib v4.21.0 (June 2025) - Latest available")
    print("\nYour project uses: Mathlib v4.24.0 (October 2025)")

    if not info['active_exists']:
        print(f"\n⚠ Warning: Active toolchain {info['active']} data not found!")
        print(f"   Download it with: uv run scripts/download_leanexplore_040.py")


async def main():
    parser = argparse.ArgumentParser(
        description="LeanExplore semantic search CLI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --info                                           # Show toolchain info
  %(prog)s "commutativity of addition"                      # Search (auto-verified by default)
  %(prog)s "digits of natural number" --no-verify           # Search without verification (faster)
  %(prog)s "addition" --toolchain 0.4.0                     # Search with specific toolchain
  %(prog)s --file query.txt --limit 10                      # Search from file
  %(prog)s "continuous function composition" --json         # JSON output
        """
    )
    parser.add_argument(
        "query",
        nargs="?",
        help="Search query (natural language description of theorem)"
    )
    parser.add_argument(
        "--info",
        action="store_true",
        help="Show toolchain information and exit"
    )
    parser.add_argument(
        "--toolchain", "-t",
        type=str,
        help="Toolchain version to use (e.g., '0.4.0' for Mathlib 4.21.0, '0.2.0' for Mathlib 4.19.0)"
    )
    parser.add_argument(
        "--file", "-f",
        type=str,
        help="Read query from file instead of argument"
    )
    parser.add_argument(
        "--limit", "-n",
        type=int,
        default=10,
        help="Maximum number of results (default: 10)"
    )
    parser.add_argument(
        "--json", "-j",
        action="store_true",
        help="Output results as JSON"
    )
    parser.add_argument(
        "--package", "-p",
        type=str,
        action="append",
        help="Filter by package (can be specified multiple times)"
    )
    parser.add_argument(
        "--no-verify",
        action="store_true",
        help="Skip verification (faster but may return theorems that don't exist in v4.24.0)"
    )

    args = parser.parse_args()

    # Handle --info flag
    if args.info:
        show_toolchain_info()
        return

    # Set toolchain version if specified
    if args.toolchain:
        if not lean_defaults:
            print("Error: lean-xplore package not available", file=sys.stderr)
            sys.exit(1)

        toolchains_dir = lean_defaults.LEAN_EXPLORE_TOOLCHAINS_BASE_DIR
        toolchain_dir = toolchains_dir / args.toolchain

        if not toolchain_dir.exists():
            print(f"Error: Toolchain {args.toolchain} data not found at {toolchain_dir}", file=sys.stderr)
            print(f"Available toolchains: {get_toolchain_info()['available']}", file=sys.stderr)
            print(f"\nTo download toolchain 0.4.0:", file=sys.stderr)
            print(f"  uv run scripts/download_leanexplore_040.py", file=sys.stderr)
            sys.exit(1)

        set_active_toolchain(args.toolchain)
        if not args.json:
            print(f"Using toolchain: {args.toolchain}")
    elif lean_defaults:
        # Auto-select latest available toolchain
        info = get_toolchain_info()
        if info['available']:
            latest = max(info['available'])
            if latest != info['active']:
                set_active_toolchain(latest)
                if not args.json:
                    print(f"Auto-selected latest toolchain: {latest}")

    # Get query
    if args.file:
        query = Path(args.file).read_text().strip()
    elif args.query:
        query = args.query
    else:
        parser.error("Either provide a query or use --file")

    # Truncate query for display
    display_query = query[:100] + "..." if len(query) > 100 else query

    if not args.json:
        print(f"Searching: {display_query}")
        print("-" * 60)

    try:
        # Search (with verification by default, unless --no-verify is specified)
        verify = not args.no_verify
        project_root = Path.cwd()

        results = await semantic_search(
            query=query,
            num_results=args.limit,
            package_filters=args.package,
            verify=verify,
            project_root=project_root
        )

        if args.json:
            output = {
                "query": query,
                "count": len(results),
                "verified": verify,
                "results": [
                    {
                        "name": r.name,
                        "statement": r.statement,
                        "source": r.source_file,
                        "description": r.informal_description,
                        "docstring": r.docstring
                    }
                    for r in results
                ]
            }
            print(json.dumps(output, indent=2))
        else:
            if not results:
                print("No results found.")
            else:
                print(f"Found {len(results)} results:\n")
                print(format_results_for_prompt(results, max_results=args.limit))

    except Exception as e:
        if args.json:
            print(json.dumps({"error": str(e)}))
        else:
            print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
