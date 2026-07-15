#!/usr/bin/env python3
"""POC: Recover flat tactic proofs from MCTS search and verify via check_build.

Runs the real MCTS proof search on test cases, recovers tactic proofs via
ProofSearchResult.tactic_proof(), and verifies them with PantographClient.check_build().

Usage:
    uv run python scripts/poc_tactic_recovery.py
    uv run python scripts/poc_tactic_recovery.py --case fib
    uv run python scripts/poc_tactic_recovery.py --case all --max-steps 500
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
    LemmaDiscoveryConfig,
    TopNSelector,
    ProofSearcher,
    ValidatedTacticProofStatus,
    build_dependency_graph,
    build_tactic_pool,
    discover_lemmas,
    filter_lemmas,
    goal_from_sorry_theorem,
    not_lean_internal,
    rank_symbols,
)

import logging
logging.basicConfig(level=logging.WARNING)


# ---------------------------------------------------------------------------
# Case definitions (same as test_proof_search_cases.py)
# ---------------------------------------------------------------------------

@dataclass
class CaseStudy:
    name: str
    description: str
    definitions: str
    theorems: list[str]


CASES: dict[str, CaseStudy] = {}

CASES["fib"] = CaseStudy(
    name="fib",
    description="Fibonacci accumulator equivalence",
    definitions="""\
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def fib_acc_aux : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fib_acc_aux n b (a + b)

def fib_acc (n : Nat) : Nat := fib_acc_aux n 0 1
""",
    theorems=[
        "theorem fib_acc_aux_spec (n k : Nat) :\n    fib_acc_aux n (fib k) (fib (k + 1)) = fib (n + k) := by\n  sorry\n",
        "theorem fib_acc_eq_fib (n : Nat) : fib_acc n = fib n := by\n  sorry\n",
    ],
)

CASES["fact"] = CaseStudy(
    name="fact",
    description="Factorial accumulator equivalence",
    definitions="""\
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def fact_acc_aux : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => fact_acc_aux n ((n + 1) * acc)

def fact_acc (n : Nat) : Nat := fact_acc_aux n 1
""",
    theorems=[
        "theorem fact_acc_aux_spec (n : Nat) (acc : Nat) :\n    fact_acc_aux n acc = (fact n) * acc := by\n  sorry\n",
        "theorem fact_acc_eq_fact (n : Nat) : fact_acc n = fact n := by\n  sorry\n",
    ],
)

CASES["rev"] = CaseStudy(
    name="rev",
    description="List reverse accumulator equivalence",
    definitions="""\
def myReverse : List α → List α
  | [] => []
  | x :: xs => myReverse xs ++ [x]

def revAux : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAux xs (x :: acc)

def myRev (xs : List α) : List α := revAux xs []
""",
    theorems=[
        "theorem revAux_spec (xs : List α) (acc : List α) :\n    revAux xs acc = myReverse xs ++ acc := by\n  sorry\n",
        "theorem myRev_eq_myReverse (xs : List α) : myRev xs = myReverse xs := by\n  sorry\n",
    ],
)

CASES["tree"] = CaseStudy(
    name="tree",
    description="Binary tree mirror involution and size preservation",
    definitions="""\
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def Tree.mirror : Tree α → Tree α
  | .leaf => .leaf
  | .node l v r => .node (Tree.mirror r) v (Tree.mirror l)

def Tree.size : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + Tree.size l + Tree.size r
""",
    theorems=[
        "theorem Tree.mirror_mirror (t : Tree α) : Tree.mirror (Tree.mirror t) = t := by\n  sorry\n",
        "theorem Tree.mirror_size (t : Tree α) : Tree.size (Tree.mirror t) = Tree.size t := by\n  sorry\n",
    ],
)

CASES["pow"] = CaseStudy(
    name="pow",
    description="Power function accumulator equivalence",
    definitions="""\
def myPow (b : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => b * myPow b n

def powAux (b : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => powAux b n (b * acc)

def myPowFast (b n : Nat) : Nat := powAux b n 1
""",
    theorems=[
        "theorem powAux_spec (b n : Nat) (acc : Nat) :\n    powAux b n acc = myPow b n * acc := by\n  sorry\n",
        "theorem myPowFast_eq_myPow (b n : Nat) : myPowFast b n = myPow b n := by\n  sorry\n",
    ],
)

CASES["map"] = CaseStudy(
    name="map",
    description="List map preserves length, then map-map fusion",
    definitions="""\
def myMap (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: myMap f xs

def myLength : List α → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs
""",
    theorems=[
        "theorem map_length (f : α → β) (xs : List α) :\n    myLength (myMap f xs) = myLength xs := by\n  sorry\n",
        "theorem map_map (f : β → γ) (g : α → β) (xs : List α) :\n    myMap f (myMap g xs) = myMap (f ∘ g) xs := by\n  sorry\n",
    ],
)

CASES["list_rev"] = CaseStudy(
    name="list_rev",
    description="Append assoc → rev distributes over append → rev involution",
    definitions="""\
def myApp : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: myApp xs ys

def myRev : List α → List α
  | [] => []
  | x :: xs => myApp (myRev xs) [x]
""",
    theorems=[
        "theorem app_nil (xs : List α) : myApp xs [] = xs := by\n  sorry\n",
        "theorem app_assoc (xs ys zs : List α) :\n    myApp (myApp xs ys) zs = myApp xs (myApp ys zs) := by\n  sorry\n",
        "theorem rev_app (xs ys : List α) :\n    myRev (myApp xs ys) = myApp (myRev ys) (myRev xs) := by\n  sorry\n",
        "theorem rev_rev (xs : List α) : myRev (myRev xs) = xs := by\n  sorry\n",
    ],
)


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

@dataclass
class TheoremResult:
    thm_name: str
    sorry_theorem: str
    solved: bool
    tactic_proof: str
    verified: bool


async def run_case(case: CaseStudy, max_steps: int) -> list[TheoremResult]:
    client = PantographClient(
        imports=["Init"], project_path="llmgen-experiments/",
        options={"printSorryGoals": True, "printDependentMVars": True},
        core_options=PANTOGRAPH_CORE_OPTIONS,
        timeout=120,
    )
    results: list[TheoremResult] = []
    try:
        searcher = ProofSearcher(client)
        new_consts, user_consts, user_ctors = await client.discover_user_constants(
            case.name, case.definitions,
        )
        if new_consts:
            dep_graph = await build_dependency_graph(client, new_consts)
            ranked = await rank_symbols(new_consts, dep_graph, client, is_relevant=not_lean_internal)
            discovery_cfg = LemmaDiscoveryConfig()
            selector = TopNSelector()
            raw_lemmas = await discover_lemmas(ranked, config=discovery_cfg)
            filtered = await filter_lemmas(raw_lemmas, client, select=selector)
            lemma_names = [r.name for r in filtered]
        else:
            lemma_names, user_consts, user_ctors = [], [], []
        searcher.tactic_pool = build_tactic_pool(lemma_names, user_consts, user_ctors)

        for sorry_thm in case.theorems:
            thm_name = sorry_thm.strip().split()[1]

            try:
                goal = goal_from_sorry_theorem(sorry_thm)
            except Exception as e:
                print(f"  {thm_name}: FAILED (goal parse error: {e})")
                results.append(TheoremResult(thm_name, sorry_thm, False, "", False))
                continue

            validated = await searcher.search_validated_tactic_proof(goal, max_steps=max_steps)
            result = validated.search_result
            status = validated.status
            tactic_proof = validated.tactic_proof
            verified = status == ValidatedTacticProofStatus.VERIFIED

            if status == ValidatedTacticProofStatus.RECOVERY_FAILED:
                print(f"  {thm_name}: SOLVED in {result.steps} steps ({result.duration:.1f}s)")
                print("    tactic recovery: ✗")
            elif status in (ValidatedTacticProofStatus.VERIFIED, ValidatedTacticProofStatus.BUILD_FAILED) and tactic_proof is not None:
                print(f"  {thm_name}: SOLVED in {result.steps} steps ({result.duration:.1f}s)")
                print(f"    theorem:\n{tactic_proof.rstrip()}")
                print(f"    tactics: {result.recover_tactics()}")
                print(f"    check_build: {'✓' if verified else '✗'}")

                if validated.build_result is not None and not validated.build_result.typechecks:
                    for d in validated.build_result.diagnostics:
                        print(f"      {d.severity}: {d.message}")

                # Load into env for subsequent theorems
                if verified:
                    names = await searcher.add_definitions(thm_name, tactic_proof)
                    searcher.add_tactics(
                        [f"apply {n}" for n in names]
                        + [f"rw [{n}]" for n in names]
                        + [f"simp only [{n}]" for n in names]
                    )
            else:
                print(f"  {thm_name}: FAILED ({result.steps} steps, {result.duration:.1f}s)")

            results.append(TheoremResult(
                thm_name, sorry_thm, result.success, tactic_proof or "", verified,
            ))
    finally:
        client.close()
    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", "-c", choices=list(CASES.keys()) + ["all"], default="all")
    parser.add_argument("--max-steps", "-s", type=int, default=500)
    args = parser.parse_args()

    cases = list(CASES.values()) if args.case == "all" else [CASES[args.case]]

    all_results: list[TheoremResult] = []

    for case in cases:
        print(f"\n{'='*60}")
        print(f"{case.name}: {case.description}")
        print(f"{'='*60}")

        thm_results = await run_case(case, args.max_steps)
        all_results.extend(thm_results)

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    solved = sum(1 for r in all_results if r.solved)
    verified = sum(1 for r in all_results if r.verified)
    for r in all_results:
        s = "✓" if r.solved else "✗"
        v = "✓" if r.verified else "✗"
        print(f"  {s} solved  {v} verified  {r.thm_name}")
    print(f"\n  {solved}/{len(all_results)} solved, {verified}/{len(all_results)} verified")

    # Assert: every solved case must pass check_build
    broken = [r.thm_name for r in all_results if r.solved and not r.verified]
    if broken:
        print(f"\n  ‼ RECOVERY BROKEN: {broken}")
        sys.exit(1)
    else:
        print(f"\n  ✓ All solved proofs pass check_build")


if __name__ == "__main__":
    asyncio.run(main())
