#!/usr/bin/env python3
"""Standalone Pantograph initialization test.

Tests that the Pantograph server can start and communicate with the Lean
project. Run from the project root (where lakefile.lean lives):

    uv run python scripts/test_pantograph.py [--project /path/to/lean/project]
    uv run python scripts/test_pantograph.py --imports Init Mathlib.Tactic

If the server fails to start, this script prints detailed diagnostics
instead of just the cryptic "Server failed to emit ready signal" assertion.
"""

import argparse
import asyncio
import shutil
import subprocess
import sys
import time
from pathlib import Path


def check_lean_toolchain(project_path: str) -> None:
    """Print Lean toolchain info for the project."""
    toolchain_file = Path(project_path) / "lean-toolchain"
    if toolchain_file.exists():
        toolchain = toolchain_file.read_text().strip()
        print(f"  lean-toolchain: {toolchain}")
    else:
        print("  lean-toolchain: NOT FOUND (no lean-toolchain file)")

    # Check if lean is on PATH
    lean_path = shutil.which("lean")
    if lean_path:
        try:
            result = subprocess.run(
                ["lean", "--version"], capture_output=True, text=True, timeout=10
            )
            print(f"  lean --version: {result.stdout.strip()}")
        except Exception as e:
            print(f"  lean --version: FAILED ({e})")
    else:
        print("  lean: NOT FOUND on PATH")

    # Check if lake is on PATH
    lake_path = shutil.which("lake")
    if lake_path:
        print(f"  lake: {lake_path}")
    else:
        print("  lake: NOT FOUND on PATH")


def check_lake_build(project_path: str) -> bool:
    """Run a quick lake build to check project health."""
    print("\n[2/4] Checking lake build...")
    try:
        result = subprocess.run(
            ["lake", "build"],
            capture_output=True,
            text=True,
            timeout=300,
            cwd=project_path,
        )
        if result.returncode == 0:
            print("  lake build: OK")
            return True
        else:
            print(f"  lake build: FAILED (exit code {result.returncode})")
            # Show last 10 lines of stderr
            lines = result.stderr.strip().split("\n")
            for line in lines[-10:]:
                print(f"    {line}")
            return False
    except subprocess.TimeoutExpired:
        print("  lake build: TIMED OUT (300s)")
        return False
    except FileNotFoundError:
        print("  lake build: FAILED (lake not found)")
        return False


async def test_pantograph_init(
    project_path: str,
    imports: list[str],
    timeout: int,
) -> bool:
    """Try to initialize Pantograph and report detailed errors."""
    print(f"\n[3/4] Initializing Pantograph server...")
    print(f"  project_path: {project_path}")
    print(f"  imports: {imports}")
    print(f"  timeout: {timeout}s")

    try:
        from pantograph.server import Server
    except ImportError:
        print("  ERROR: pantograph package not installed")
        print("  Try: uv add pantograph")
        return False

    options = {
        "printSorryGoals": True,
        "printDependentMVars": True,
        "printExprAst": True,
    }

    t0 = time.monotonic()
    try:
        server = await Server.create(
            imports=imports,
            project_path=project_path,
            options=options,
            timeout=timeout,
        )
        elapsed = time.monotonic() - t0
        print(f"  Server created OK in {elapsed:.1f}s")
    except AssertionError as e:
        elapsed = time.monotonic() - t0
        msg = str(e)
        print(f"  FAILED after {elapsed:.1f}s")
        print(f"  Error: {msg}")
        print()
        print("  Likely causes:")
        if "ready signal" in msg:
            print("    1. Lean version mismatch between project and Pantograph")
            print("       - Check lean-toolchain vs pantograph's expected version")
            print("    2. Imports failed to load (missing dependency)")
            print("       - Try with --imports Init to test minimal imports")
            print("    3. Lean process crashed on startup")
            print("       - Run 'lake build' first to check project health")
            print("    4. Timeout too short for heavy imports")
            print(f"       - Current timeout: {timeout}s, try --timeout 120")
        return False
    except Exception as e:
        elapsed = time.monotonic() - t0
        print(f"  FAILED after {elapsed:.1f}s")
        print(f"  Error ({type(e).__name__}): {e}")
        return False

    # Step 4: Try a simple operation
    print(f"\n[4/4] Testing basic operation (goal_start with 'True')...")
    try:
        state = await server.goal_start_async("True")
        print(f"  goal_start: OK (state id: {state.state_id})")

        # Try a tactic
        result = await server.goal_tactic_async(state, "trivial")
        print(f"  goal_tactic 'trivial': OK (solved: {result.is_solved})")
        return True
    except Exception as e:
        print(f"  Basic operation FAILED: {type(e).__name__}: {e}")
        return False


def find_project_root(start: str) -> str:
    """Walk up from start to find lakefile.lean."""
    path = Path(start).resolve()
    if path.is_file():
        path = path.parent
    while path != path.parent:
        if (path / "lakefile.lean").exists() or (path / "lakefile.toml").exists():
            return str(path)
        path = path.parent
    raise FileNotFoundError(
        f"No lakefile.lean found in parents of {start}. "
        "Run this from within a Lean project or pass --project."
    )


def main():
    parser = argparse.ArgumentParser(
        description="Test Pantograph server initialization against a Lean project"
    )
    parser.add_argument(
        "lean_project",
        nargs="?",
        default=".",
        help="Path to Lean project root with lakefile.lean or lakefile.toml (default: current directory)",
    )
    parser.add_argument(
        "--imports",
        nargs="+",
        default=None,
        help="Lean imports for Pantograph (default: runtime session imports)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="Server creation timeout in seconds (default: 60)",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="Skip the lake build check",
    )
    args = parser.parse_args()

    try:
        project_path = find_project_root(args.lean_project)
    except FileNotFoundError as e:
        print(f"ERROR: {e}")
        sys.exit(1)

    # Default imports mirror runtime Pantograph session imports
    if args.imports is None:
        imports = ["Velvet.Std", "Extensions.Tactics", "Extensions.SpecDSL", "Mathlib.Tactic"]
    else:
        imports = args.imports

    print("=" * 60)
    print("Pantograph Initialization Test")
    print("=" * 60)

    print(f"\n[1/4] Checking Lean environment...")
    print(f"  project: {project_path}")
    check_lean_toolchain(project_path)

    if not args.skip_build:
        build_ok = check_lake_build(project_path)
        if not build_ok:
            print("\n  WARNING: lake build failed — Pantograph will likely fail too")
            print("  Fix build errors first, or use --skip-build to skip this check")
    else:
        print("\n[2/4] Skipping lake build check (--skip-build)")

    ok = asyncio.run(test_pantograph_init(project_path, imports, args.timeout))

    print()
    print("=" * 60)
    if ok:
        print("RESULT: ALL CHECKS PASSED")
    else:
        print("RESULT: FAILED — see diagnostics above")
    print("=" * 60)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
