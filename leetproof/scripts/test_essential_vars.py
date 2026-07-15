#!/usr/bin/env python3
"""Test cases for find_essential_vars / minimize_goal.

Usage:
    uv run python scripts/test_essential_vars.py
"""

from __future__ import annotations

import asyncio
import logging
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.pantograph_client import PantographClient
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS
from utils.lean.unused_var_removal import find_essential_vars, minimize_goal

logging.basicConfig(level=logging.WARNING)


@dataclass
class TestCase:
    name: str
    sorry_theorem: str
    expected_essential: set[str]
    expected_removed: set[str]


CASES = [
    # 1. z is irrelevant — not in goal, no one depends on it
    TestCase(
        name="drop_irrelevant",
        sorry_theorem=(
            "theorem test1 (n k z : Nat) : n + k = k + n := by sorry"
        ),
        expected_essential={"n", "k"},
        expected_removed={"z"},
    ),
    # 2. hx says something about essential x — forward pass keeps it
    TestCase(
        name="keep_hypothesis_about_essential",
        sorry_theorem=(
            "theorem test2 (x : Nat) (hx : x > 0) : x = x := by sorry"
        ),
        expected_essential={"x", "hx"},
        expected_removed=set(),
    ),
    # 3. z : v + x = 0 promoted (forward, mentions x).
    #    v promoted (backward, z's type mentions v).
    TestCase(
        name="backward_pass_transitive",
        sorry_theorem=(
            "theorem test3 (v x : Nat) (hx : x > 0) "
            "(z : v + x = 0) : x = x := by sorry"
        ),
        expected_essential={"x", "hx", "z", "v"},
        expected_removed=set(),
    ),
    # 4. Chain: hab links a-b, hbc links b-c.  w is irrelevant.
    #    Forward from {a,c} promotes hab, hbc.
    #    Backward from b: revert b also reverts hab & hbc (essential) → b promoted.
    TestCase(
        name="chain_with_irrelevant",
        sorry_theorem=(
            "theorem test4 (a b c : Nat) "
            "(hab : a = b) (hbc : b = c) (w : Nat) : a = c := by sorry"
        ),
        expected_essential={"a", "b", "c", "hab", "hbc"},
        expected_removed={"w"},
    ),
]


async def run_case(
    case: TestCase, client: PantographClient
) -> bool:
    """Run one test case.  Returns True on pass."""
    print(f"\n{'='*60}")
    print(f"Test: {case.name}")
    print(f"{'='*60}")
    print(f"  {case.sorry_theorem}")

    server = await client.get_server()
    goal_state = await client.load_sorry(case.sorry_theorem)
    if goal_state is None:
        print("  SKIP: could not load sorry")
        return False

    goal = goal_state.goals[0]
    print(f"\n  Context:")
    for v in goal.variables:
        print(f"    {v.name} : {v.t}")
    print(f"  Goal: {goal.target}")

    # --- find_essential_vars ---
    essential = await find_essential_vars(goal_state, server)
    print(f"\n  Essential vars: {sorted(essential)}")

    # --- minimize_goal ---
    thm_name = case.sorry_theorem.strip().split()[1]
    goal_objs = client.goals_from_state(goal_state, prefix=thm_name)
    original_goal = goal_objs[0]
    minimized = await minimize_goal(original_goal, goal_state, server)

    print(f"\n  Original:  {original_goal.as_theorem()}")
    print(f"  Minimized: {minimized.as_theorem()}")

    removed = {p.name for p in original_goal.params} - {
        p.name for p in minimized.params
    }
    print(f"  Removed: {sorted(removed) if removed else '(none)'}")

    # --- assertions ---
    ok = True
    if essential != case.expected_essential:
        print(
            f"\n  FAIL essential: expected {sorted(case.expected_essential)}, "
            f"got {sorted(essential)}"
        )
        ok = False
    if removed != case.expected_removed:
        print(
            f"\n  FAIL removed: expected {sorted(case.expected_removed)}, "
            f"got {sorted(removed)}"
        )
        ok = False

    print(f"\n  {'PASS' if ok else 'FAIL'}")
    return ok


async def main():
    client = PantographClient(
        imports=["Init"],
        project_path="llmgen-experiments/",
        options={
            "printSorryGoals": True,
            "printDependentMVars": True,
            "printExprAST": True,
        },
        core_options=PANTOGRAPH_CORE_OPTIONS,
        timeout=120,
    )
    try:
        passed = 0
        for case in CASES:
            if await run_case(case, client):
                passed += 1

        total = len(CASES)
        print(f"\n{'='*60}")
        print(f"Results: {passed}/{total} passed")
        print(f"{'='*60}")
        if passed < total:
            sys.exit(1)
    finally:
        client.close()


if __name__ == "__main__":
    asyncio.run(main())
