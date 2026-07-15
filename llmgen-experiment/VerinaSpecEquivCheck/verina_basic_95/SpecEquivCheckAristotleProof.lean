/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: eb1405d9-be8f-4488-b950-78d41efd83c1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (i : Int) (j : Int) : VerinaSpec.swap_precond arr i j ↔ LLMSpec.precondition arr i j

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (i : Int) (j : Int) (result : Array Int) : LLMSpec.precondition arr i j →
  (VerinaSpec.swap_postcond arr i j result ↔ LLMSpec.postcondition arr i j result)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Mathlib.Tactic


namespace VerinaSpec

def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size

def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) :=
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)

end VerinaSpec

namespace LLMSpec

-- Helper: convert an Int index (assumed nonnegative) to a Nat index.
def idx (k : Int) : Nat := Int.toNat k

-- Helper: the pointwise characterization of swapping indices i and j in arr.
def swapValueAt (arr : Array Int) (iN : Nat) (jN : Nat) (k : Nat) : Int :=
  if k = iN then arr[jN]!
  else if k = jN then arr[iN]!
  else arr[k]!

-- Preconditions: indices are non-negative and within array bounds.
def precondition (arr : Array Int) (i : Int) (j : Int) : Prop :=
  (0 ≤ i) ∧ (0 ≤ j) ∧ (idx i < arr.size) ∧ (idx j < arr.size)

-- Postconditions: result has same size and matches a swap at i and j.
def postcondition (arr : Array Int) (i : Int) (j : Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ k : Nat, k < arr.size →
    result[k]! = swapValueAt arr (idx i) (idx j) k)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (i : Int) (j : Int) : VerinaSpec.swap_precond arr i j ↔ LLMSpec.precondition arr i j := by
  -- By definition of `swap_precond` and `precondition`, they are equivalent because they both require the indices to be non-negative and within the array's bounds.
  simp [VerinaSpec.swap_precond, LLMSpec.precondition];
  -- Since `i` and `j` are non-negative, their `toNat` values are just `i` and `j` themselves.
  intro hi hj
  simp [LLMSpec.idx, hi, hj]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (i : Int) (j : Int) (result : Array Int) : LLMSpec.precondition arr i j →
  (VerinaSpec.swap_postcond arr i j result ↔ LLMSpec.postcondition arr i j result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where the array has two distinct elements.
  use #[1, 2];
  -- Choose indices i = 0 and j = 1.
  use 0, 1;
  -- Let's simplify the goal.
  simp +decide [LLMSpec.precondition, LLMSpec.postcondition, VerinaSpec.swap_postcond];
  -- Let's choose the result array to be [2, 1, 3].
  use #[2, 1, 3];
  -- Let's simplify the goal. We need to show that the postcondition holds for the given array and indices.
  simp +decide [LLMSpec.swapValueAt]

-/
theorem postcondition_equiv (arr : Array Int) (i : Int) (j : Int) (result : Array Int) : LLMSpec.precondition arr i j →
  (VerinaSpec.swap_postcond arr i j result ↔ LLMSpec.postcondition arr i j result) := by
  sorry

end Proof