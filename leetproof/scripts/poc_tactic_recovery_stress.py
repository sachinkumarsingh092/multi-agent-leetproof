#!/usr/bin/env python3
"""Stress test: tactic recovery with crafted tactic pools and complex proofs.

Uses ProofSearchMCTS with hand-crafted tactic pools containing winning
tactics + noise, then verifies recovered proofs with check_build.

Usage:
    uv run python scripts/poc_tactic_recovery_stress.py
    uv run python scripts/poc_tactic_recovery_stress.py --case multi_close
"""

from __future__ import annotations

import argparse
import asyncio
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.pantograph_client import PantographClient
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS
from tools.proof_search import (
    ProofSearcher,
    ValidatedTacticProofStatus,
    WeightedTactic,
    TACTIC_WEIGHT_CORE,
    TACTIC_WEIGHT_LEMMA,
    goal_from_sorry_theorem,
)

import logging
logging.basicConfig(level=logging.WARNING)


# ---------------------------------------------------------------------------
# Test cases
# ---------------------------------------------------------------------------

@dataclass
class StressCase:
    name: str
    description: str
    lean_preamble: str
    sorry_theorem: str
    winning_tactics: list[str]
    noise_tactics: list[str]


CASES: dict[str, StressCase] = {}

CASES["multi_close"] = StressCase(
    name="multi_close",
    description="simp closing multiple goals from a constructor split",
    lean_preamble="",
    sorry_theorem="theorem multi_close (n : Nat) : n = n ∧ n + 0 = n ∧ 0 + n = n := by\n  sorry\n",
    winning_tactics=["constructor", "rfl", "constructor", "omega", "simp"],
    noise_tactics=["ring", "apply And.intro", "intro h", "cases n", "exact n"],
)

CASES["cases_omega"] = StressCase(
    name="cases_omega",
    description="cases on Bool then omega/decide on each branch",
    lean_preamble="def boolToNat : Bool → Nat\n  | true => 1\n  | false => 0\n",
    sorry_theorem="theorem boolToNat_le_one (b : Bool) : boolToNat b ≤ 1 := by\n  sorry\n",
    winning_tactics=["cases b", "simp [boolToNat]", "decide", "omega"],
    noise_tactics=["rfl", "ring", "constructor", "intro", "apply Nat.le_refl"],
)

CASES["semicolon_combinator"] = StressCase(
    name="semicolon_combinator",
    description="induction n <;> simp closes all branches at once",
    lean_preamble="def addOne : Nat → Nat\n  | 0 => 1\n  | n + 1 => (addOne n) + 1\n",
    sorry_theorem="theorem addOne_eq (n : Nat) : addOne n = n + 1 := by\n  sorry\n",
    winning_tactics=["induction n <;> expose_names", "simp [addOne]", "simp_all [addOne]", "omega"],
    noise_tactics=["rfl", "ring", "constructor", "cases n", "intro h"],
)

CASES["deep_and"] = StressCase(
    name="deep_and",
    description="((A ∧ B) ∧ (C ∧ D)) — balanced tree of constructors",
    lean_preamble="",
    sorry_theorem="theorem deep_and (a b c d : Prop) (ha : a) (hb : b) (hc : c) (hd : d) :\n    (a ∧ b) ∧ (c ∧ d) := by\n  sorry\n",
    winning_tactics=["constructor", "exact ha", "exact hb", "exact hc", "exact hd", "assumption"],
    noise_tactics=["intro", "apply Or.inl", "left", "right", "simp", "omega", "rfl"],
)

CASES["iff_proof"] = StressCase(
    name="iff_proof",
    description="Iff.intro creates two goals (forward + backward)",
    lean_preamble="",
    sorry_theorem="theorem iff_and_comm (p q : Prop) : p ∧ q ↔ q ∧ p := by\n  sorry\n",
    winning_tactics=["constructor", "intro h", "exact ⟨h.2, h.1⟩", "simp [And.comm]", "aesop"],
    noise_tactics=["rfl", "ring", "omega", "cases p", "intro", "simp", "constructor"],
)

CASES["sum_acc"] = StressCase(
    name="sum_acc",
    description="Sum accumulator with induction + generalizing",
    lean_preamble="def sumTo : Nat → Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + sumTo n\n\ndef sumAux : Nat → Nat → Nat\n  | 0, acc => acc\n  | n + 1, acc => sumAux n (acc + (n + 1))\n",
    sorry_theorem="theorem sumAux_spec (n acc : Nat) : sumAux n acc = sumTo n + acc := by\n  sorry\n",
    winning_tactics=["induction n generalizing acc <;> expose_names", "simp [sumTo, sumAux]", "simp_all [sumTo, sumAux]", "omega", "grind"],
    noise_tactics=["rfl", "ring", "constructor", "cases n", "intro", "exact acc"],
)

CASES["or_elim"] = StressCase(
    name="or_elim",
    description="cases on an Or hypothesis creates two subgoals",
    lean_preamble="",
    sorry_theorem="theorem or_comm_test (p q : Prop) (h : p ∨ q) : q ∨ p := by\n  sorry\n",
    winning_tactics=["cases h", "apply Or.inr", "apply Or.inl", "assumption", "exact Or.symm h", "aesop", "simp_all"],
    noise_tactics=["rfl", "omega", "constructor", "intro", "ring", "exact h"],
)

CASES["append_assoc"] = StressCase(
    name="append_assoc",
    description="List append assoc — induction with congruence",
    lean_preamble="def myApp : List α → List α → List α\n  | [], ys => ys\n  | x :: xs, ys => x :: myApp xs ys\n",
    sorry_theorem="theorem myApp_assoc (xs ys zs : List α) :\n    myApp (myApp xs ys) zs = myApp xs (myApp ys zs) := by\n  sorry\n",
    winning_tactics=["induction xs <;> expose_names", "simp [myApp]", "simp_all [myApp]", "rfl"],
    noise_tactics=["omega", "ring", "constructor", "cases xs", "intro h", "unfold myApp"],
)

CASES["max_comm"] = StressCase(
    name="max_comm",
    description="max commutativity — needs split on if/match",
    lean_preamble="def myMax (a b : Nat) : Nat := if a ≤ b then b else a\n",
    sorry_theorem="theorem myMax_comm (a b : Nat) : myMax a b = myMax b a := by\n  sorry\n",
    winning_tactics=["simp [myMax]", "split <;> expose_names", "omega", "grind", "simp_all [myMax]"],
    noise_tactics=["rfl", "ring", "constructor", "intro", "cases a", "exact a"],
)

CASES["five_and"] = StressCase(
    name="five_and",
    description="A ∧ B ∧ C ∧ D ∧ E — 4x constructor + 5x exact/assumption",
    lean_preamble="",
    sorry_theorem="theorem five_and (a b c d e : Prop) (ha : a) (hb : b) (hc : c) (hd : d) (he : e) :\n    a ∧ b ∧ c ∧ d ∧ e := by\n  sorry\n",
    winning_tactics=["constructor", "assumption", "exact ha", "exact hb", "exact hc", "exact hd", "exact he"],
    noise_tactics=["intro", "cases ha", "apply Or.inl", "simp", "omega", "rfl", "aesop"],
)


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def build_pool(case: StressCase) -> list[WeightedTactic]:
    pool: list[WeightedTactic] = []
    seen: set[str] = set()
    for t in case.winning_tactics:
        if t not in seen:
            seen.add(t)
            pool.append(WeightedTactic(t, TACTIC_WEIGHT_CORE))
    for t in case.noise_tactics:
        if t not in seen:
            seen.add(t)
            pool.append(WeightedTactic(t, TACTIC_WEIGHT_LEMMA))
    return pool


async def run_case(
    client: PantographClient,
    case: StressCase,
    max_steps: int,
) -> tuple[bool, bool]:
    """Returns (solved, verified)."""
    if case.lean_preamble.strip():
        await client.load_definitions(case.name, case.lean_preamble)

    pool = build_pool(case)
    searcher = ProofSearcher(client, tactic_pool=pool)

    try:
        goal = goal_from_sorry_theorem(case.sorry_theorem)
    except Exception as e:
        print(f"  ERROR: could not parse sorry theorem: {e}")
        return False, False

    validated = await searcher.search_validated_tactic_proof(goal, max_steps=max_steps)
    result = validated.search_result
    status = validated.status

    if status == ValidatedTacticProofStatus.SEARCH_FAILED:
        print(f"  ✗ MCTS failed after {result.steps} steps ({result.duration:.1f}s)")
        return False, False

    if status == ValidatedTacticProofStatus.RECOVERY_FAILED:
        print(f"  SOLVED in {result.steps} steps ({result.duration:.1f}s)")
        print("    tactic recovery: ✗")
        return True, False

    print(f"  SOLVED in {result.steps} steps ({result.duration:.1f}s)")
    if validated.tactic_proof:
        print(f"    theorem:\n{validated.tactic_proof.rstrip()}")
    print(f"    tactics: {result.recover_tactics()}")
    print(f"    check_build: {'✓' if status == ValidatedTacticProofStatus.VERIFIED else '✗'}")

    if status == ValidatedTacticProofStatus.BUILD_FAILED and validated.build_result is not None:
        if validated.tactic_proof:
            print(f"    recovered proof:\n{validated.tactic_proof}")
        for d in validated.build_result.diagnostics:
            print(f"      {d.severity}: {d.message}")

    return True, status == ValidatedTacticProofStatus.VERIFIED


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", "-c", choices=list(CASES.keys()) + ["all"], default="all")
    parser.add_argument("--max-steps", "-s", type=int, default=500)
    args = parser.parse_args()

    cases = list(CASES.values()) if args.case == "all" else [CASES[args.case]]

    client = PantographClient(
        imports=["Init"], project_path="llmgen-experiments/",
        options={"printSorryGoals": True, "printDependentMVars": True},
        core_options=PANTOGRAPH_CORE_OPTIONS,
        timeout=120,
    )

    results: list[tuple[str, bool, bool]] = []
    try:
        for case in cases:
            print(f"\n{'='*60}")
            print(f"{case.name}: {case.description}")
            print(f"{'='*60}")
            solved, verified = await run_case(client, case, args.max_steps)
            results.append((case.name, solved, verified))
    finally:
        client.close()

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    for name, solved, verified in results:
        s = "✓" if solved else "✗"
        v = "✓" if verified else "✗"
        print(f"  {s} solved  {v} verified  {name}")
    solved_n = sum(1 for _, s, _ in results if s)
    verified_n = sum(1 for _, _, v in results if v)
    print(f"\n  {solved_n}/{len(results)} solved, {verified_n}/{len(results)} verified")

    broken = [n for n, s, v in results if s and not v]
    if broken:
        print(f"\n  ‼ RECOVERY BROKEN: {broken}")
        sys.exit(1)
    else:
        print(f"\n  ✓ All solved proofs pass check_build")


if __name__ == "__main__":
    asyncio.run(main())
