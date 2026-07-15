"""Test script to check whether Pantograph's load_sorry preserves expose_names effects."""

import asyncio
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from tools.pantograph_client import PantographClient
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS, VELVET_IMPORTS, PANTOGRAPH_OPTIONS


# Just specs + the proof sketch, no imports (Pantograph handles imports separately)
SKETCH_WITH_EXPOSE = """\
section Specs
def precondition (list : List (List Int)) : Prop :=
  True

def postcondition (list : List (List Int)) (res : Int) : Prop :=
  (0 ≤ res) ∧
  ((list = []) → res = 0) ∧
  ((list ≠ []) →
      (∃ i : Nat, i < list.length ∧ res = (list[i]!).length) ∧
      (∀ i : Nat, i < list.length → (list[i]!).length ≤ res))
end Specs

set_option maxHeartbeats 10000000

theorem goal_2
    (list : List (List ℤ))
    (require_1 : precondition list)
    (if_neg : ¬list = [])
    (i : ℕ)
    (mx : ℕ)
    (a : 1 ≤ i)
    (a_1 : i ≤ list.length)
    (i_1 : ℕ)
    (mx_1 : ℕ)
    (invariant_mx_is_from_prefix : ∃ j < i, mx = (list[j]?.getD default).length)
    (invariant_mx_upper_bound_prefix : ∀ j < i, (list[j]?.getD default).length ≤ mx)
    (done_1 : list.length ≤ i)
    (i_2 : i = i_1 ∧ mx = mx_1)
    : postcondition list ↑mx_1 := by
  unfold postcondition
  have hi_eq_len : i = list.length := by expose_names; sorry
  have hmx_eq_mx1 : mx = mx_1 := by expose_names; sorry
  have hnonneg : (0 : Int) ≤ (↑mx_1 : Int) := by expose_names; sorry
  have hempty : (list = []) → (↑mx_1 : Int) = 0 := by expose_names; sorry
  rcases invariant_mx_is_from_prefix with ⟨j, hj_lt_i, hmx_def⟩
  have hj_lt_len : j < list.length := by expose_names; sorry
  have hres_eq_len : (↑mx_1 : Int) = (list[j]!).length := by expose_names; sorry
  have hexists : ∃ idx : Nat, idx < list.length ∧ (↑mx_1 : Int) = (list[idx]!).length := by
    exact ⟨j, hj_lt_len, hres_eq_len⟩
  have hupper : ∀ idx : Nat, idx < list.length → (list[idx]!).length ≤ (↑mx_1 : Int) := by expose_names; sorry
  have hnonempty :
      (list ≠ []) →
        ( (∃ idx : Nat, idx < list.length ∧ (↑mx_1 : Int) = (list[idx]!).length) ∧
          (∀ idx : Nat, idx < list.length → (list[idx]!).length ≤ (↑mx_1 : Int)) ) := by
    intro _
    exact And.intro hexists hupper
  refine And.intro hnonneg ?_
  refine And.intro hempty ?_
  exact hnonempty
"""

# Same sketch but WITHOUT expose_names (just sorry)
SKETCH_WITHOUT_EXPOSE = SKETCH_WITH_EXPOSE.replace("expose_names; sorry", "sorry")


async def test_goals(label: str, lean_code: str):
    print(f"\n{'='*80}")
    print(f"  {label}")
    print(f"{'='*80}")

    client = PantographClient(
        imports=VELVET_IMPORTS,
        project_path="llmgen-experiments/",
        options=PANTOGRAPH_OPTIONS,
        core_options=PANTOGRAPH_CORE_OPTIONS,
        timeout=240,
    )
    try:
        goal_state = await client.load_sorry(lean_code)
        if goal_state is None:
            print("  ERROR: load_sorry returned None (compilation error?)")
            return

        print(f"  Found {len(goal_state.goals)} sorry goals\n")
        for i, g in enumerate(goal_state.goals):
            print(f"  --- Goal {i} (id={g.id}) ---")
            ghost_vars = [v for v in g.variables if v.name and "✝" in v.name]
            for v in g.variables:
                if v.name:
                    marker = "  <<<< GHOST" if "✝" in v.name else ""
                    print(f"    ({v.name} : {v.t}){marker}")
            print(f"    : {g.target}")
            if ghost_vars:
                print(f"    ** GHOST VARIABLES FOUND: {[v.name for v in ghost_vars]} **")
            else:
                print(f"    (no ghost variables)")
            print()
    finally:
        client.close()


async def main():
    print("Testing ghost variable exposure through Pantograph load_sorry")
    await test_goals("WITH expose_names; sorry", SKETCH_WITH_EXPOSE)
    await test_goals("WITHOUT expose_names (just sorry)", SKETCH_WITHOUT_EXPOSE)


if __name__ == "__main__":
    asyncio.run(main())
