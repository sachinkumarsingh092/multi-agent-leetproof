#!/usr/bin/env python3
"""Proof search case studies.

Each case defines some Lean code, then proves a sequence of theorems
incrementally — each proven theorem is loaded into the environment
before attempting the next.

Usage:
    uv run python scripts/test_proof_search_cases.py
    uv run python scripts/test_proof_search_cases.py --case fib
    uv run python scripts/test_proof_search_cases.py --max-steps 300

Visualization:
    Pass ``--visualize`` (or ``-v``) to generate an interactive HTML file
    for each theorem's MCTS search tree.  Files are written to
    ``output/viz/`` by default (override with ``--viz-dir``).

        uv run python scripts/test_proof_search_cases.py --case fib -v
        uv run python scripts/test_proof_search_cases.py --visualize --viz-dir /tmp/viz

    Each HTML file is self-contained (D3.js loaded from CDN) and supports:
      - Pan/zoom on the search tree
      - Click a node to inspect its proof state, MCTS stats, and tested tactics
      - Shift-click or double-click a node to collapse/expand its subtree
      - "Proof Path" button to highlight the root-to-solution path (if solved)
      - Step slider to replay the search iteration-by-iteration

    A ``.json`` file is also saved next to each HTML file (e.g.
    ``output/viz/fib_fib_add.json``).  It contains the raw search data:
      - ``metadata``: success, steps, duration, and the full tactic pool
      - ``tree``: recursive MCTS tree with goals, hypotheses, MCTS stats,
        and tested tactics at every node
      - ``trace_steps``: per-iteration log (selected node, tactic, outcome)
      - ``proof_path``: node IDs from root to solved leaf (if found)

    You can re-render an HTML visualization from a JSON file without
    re-running the search::

        uv run python tools/proof_search_viz.py output/viz/fib_fib_add.json
"""

from __future__ import annotations

import argparse
import asyncio
import logging
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.pantograph_client import PantographClient
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS
from tools.proof_search import (
    LemmaDiscoveryConfig,
    TopNSelector,
    ProofSearchResult,
    ProofSearcher,
    ValidatedTacticProofResult,
    ValidatedTacticProofStatus,
    build_dependency_graph,
    build_tactic_pool,
    discover_lemmas,
    filter_lemmas,
    goal_from_sorry_theorem,
    not_lean_internal,
    rank_symbols,
)
from tools.proof_search_viz import generate_visualization

logging.basicConfig(level=logging.WARNING)


# ---------------------------------------------------------------------------
# Case definition
# ---------------------------------------------------------------------------

@dataclass
class CaseStudy:
    name: str
    description: str
    definitions: str
    theorems: list[str]  # sorry theorems, proved in order


CASES: dict[str, CaseStudy] = {}


# ---------------------------------------------------------------------------
# Cases
# ---------------------------------------------------------------------------

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
        """\
theorem fib_acc_aux_spec (n k : Nat) :
    fib_acc_aux n (fib k) (fib (k + 1)) = fib (n + k) := by
  sorry
""",
        """\
theorem fib_acc_eq_fib (n : Nat) : fib_acc n = fib n := by
  sorry
""",
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
        """\
theorem fact_acc_aux_spec (n : Nat) (acc : Nat) :
    fact_acc_aux n acc = (fact n) * acc := by
  sorry
""",
        """\
theorem fact_acc_eq_fact (n : Nat) : fact_acc n = fact n := by
  sorry
""",
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
        """\
theorem revAux_spec (xs : List α) (acc : List α) :
    revAux xs acc = myReverse xs ++ acc := by
  sorry
""",
        """\
theorem myRev_eq_myReverse (xs : List α) : myRev xs = myReverse xs := by
  sorry
""",
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
        """\
theorem Tree.mirror_mirror (t : Tree α) : Tree.mirror (Tree.mirror t) = t := by
  sorry
""",
        """\
theorem Tree.mirror_size (t : Tree α) : Tree.size (Tree.mirror t) = Tree.size t := by
  sorry
""",
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
        """\
theorem powAux_spec (b n : Nat) (acc : Nat) :
    powAux b n acc = myPow b n * acc := by
  sorry
""",
        """\
theorem myPowFast_eq_myPow (b n : Nat) : myPowFast b n = myPow b n := by
  sorry
""",
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
        """\
theorem map_length (f : α → β) (xs : List α) :
    myLength (myMap f xs) = myLength xs := by
  sorry
""",
        """\
theorem map_map (f : β → γ) (g : α → β) (xs : List α) :
    myMap f (myMap g xs) = myMap (f ∘ g) xs := by
  sorry
""",
    ],
)

CASES["list_rev"] = CaseStudy(
    name="list_rev",
    description="Append assoc → rev distributes over append → rev involution (4-step chain)",
    definitions="""\
def myApp : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: myApp xs ys

def myRev : List α → List α
  | [] => []
  | x :: xs => myApp (myRev xs) [x]
""",
    theorems=[
        """\
theorem app_nil (xs : List α) : myApp xs [] = xs := by
  sorry
""",
        """\
theorem app_assoc (xs ys zs : List α) :
    myApp (myApp xs ys) zs = myApp xs (myApp ys zs) := by
  sorry
""",
        """\
theorem rev_app (xs ys : List α) :
    myRev (myApp xs ys) = myApp (myRev ys) (myRev xs) := by
  sorry
""",
        """\
theorem rev_rev (xs : List α) : myRev (myRev xs) = xs := by
  sorry
""",
    ],
)


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

async def run_case(case: CaseStudy, max_steps: int, trace: bool = False) -> list[tuple[str, str, ValidatedTacticProofResult]]:
    """Returns list of (thm_name, sorry_theorem, validated_result)."""
    client = PantographClient(
        imports=["Init"], project_path="llmgen-experiments/",
        options={"printSorryGoals": True, "printDependentMVars": True},
        core_options=PANTOGRAPH_CORE_OPTIONS,
        timeout=120,
    )
    results: list[tuple[str, str, ValidatedTacticProofResult]] = []
    try:
        searcher = ProofSearcher(client)
        new_consts, user_consts, user_ctors = await client.discover_user_constants(case.name, case.definitions)
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
                print(f"  WARNING: {thm_name} theorem parse failed: {e}")
                results.append((
                    thm_name,
                    sorry_thm,
                    ValidatedTacticProofResult(search_result=ProofSearchResult(success=False)),
                ))
                continue

            validated = await searcher.search_validated_tactic_proof(goal, max_steps=max_steps, trace=trace)
            result = validated.search_result
            results.append((thm_name, sorry_thm, validated))

            # Print tactic pool from trace metadata when available.
            tactic_pool = []
            if result.trace is not None:
                tactic_pool = list(result.trace.metadata.get("tactic_pool", []))
            if tactic_pool:
                print(f"\n    Tactic pool ({len(tactic_pool)} tactics):")
                for entry in tactic_pool:
                    t = str(entry.get("tactic", ""))
                    w = float(entry.get("weight", 0.0))
                    print(f"      [{w:.1f}] {t}")

            # If proven, show recovered theorem; if verified, load into env.
            if validated.status != ValidatedTacticProofStatus.SEARCH_FAILED:
                if validated.status == ValidatedTacticProofStatus.RECOVERY_FAILED:
                    print(f"  WARNING: {thm_name} solved but tactic recovery failed")
                    continue
                if validated.tactic_proof is None:
                    continue

                print(f"    theorem:\n{validated.tactic_proof.rstrip()}")

                if validated.status == ValidatedTacticProofStatus.BUILD_FAILED:
                    print(f"  WARNING: {thm_name} recovered tactic proof failed check_build")
                    continue

                names = await searcher.add_definitions(thm_name, validated.tactic_proof)
                searcher.add_tactics(
                    [f"apply {n}" for n in names]
                    + [f"rw [{n}]" for n in names]
                    + [f"simp only [{n}]" for n in names]
                )
    finally:
        client.close()
    return results


async def main():
    parser = argparse.ArgumentParser(description="Proof search case studies")
    parser.add_argument("--case", "-c", choices=list(CASES.keys()) + ["all"], default="all")
    parser.add_argument("--max-steps", "-s", type=int, default=500)
    parser.add_argument("--visualize", "-v", action="store_true",
                        help="Generate interactive HTML visualization for each theorem")
    parser.add_argument("--viz-dir", type=str, default="output/viz",
                        help="Directory for visualization HTML files (default: output/viz)")
    args = parser.parse_args()

    cases = list(CASES.values()) if args.case == "all" else [CASES[args.case]]

    all_results: list[tuple[str, str, ValidatedTacticProofResult]] = []

    for case in cases:
        print(f"\n{'='*60}")
        print(f"{case.name}: {case.description}")
        print(f"{'='*60}")
        print(case.definitions)

        results = await run_case(case, args.max_steps, trace=args.visualize)
        for thm_name, sorry_thm, validated in results:
            result = validated.search_result
            status = "SOLVED" if result.success else "FAILED"
            print(f"  {thm_name}: {status} ({result.steps} steps, {result.duration:.1f}s)")
            if validated.status == ValidatedTacticProofStatus.RECOVERY_FAILED:
                print("  tactics: <recovery failed>")
            elif result.success and result.recover_tactics() is not None:
                print(f"  tactics: {result.recover_tactics()}")

            # Generate visualization if tracing was enabled
            if args.visualize and result.trace is not None:
                tree_data = result.trace.metadata.get("tree", {})
                viz_path = generate_visualization(
                    trace=result.trace,
                    tree=tree_data,
                    output_path=Path(args.viz_dir) / f"{case.name}_{thm_name}.html",
                    title=f"{case.name}/{thm_name}",
                )
                print(f"  Visualization: {viz_path}")

            all_results.append((case.name, thm_name, validated))

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    solved = sum(1 for _, _, vr in all_results if vr.search_result.success)
    for case_name, thm_name, vr in all_results:
        r = vr.search_result
        mark = "+" if r.success else "-"
        print(f"  [{mark}] {case_name}/{thm_name} ({r.steps} steps, {r.duration:.1f}s)")
    print(f"\n  {solved}/{len(all_results)} solved")
    if args.visualize:
        print(f"\n  Visualizations saved to: {args.viz_dir}/")


if __name__ == "__main__":
    asyncio.run(main())
