/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 53df9034-26c4-42e4-8efe-bc5a62b38385

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.dissimilarElements_precond a b ↔ LLMSpec.precondition a b

The following was negated by Aristotle:

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.dissimilarElements_postcond a b result ↔ LLMSpec.postcondition a b result)

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

import Std.Data.HashSet


namespace VerinaSpec

def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)

def dissimilarElements_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def dissimilarElements_postcond (a : Array Int) (b : Array Int) (result: Array Int) :=
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)

end VerinaSpec

namespace LLMSpec

-- Helper: array is sorted in nondecreasing order, using Nat indices and `arr[i]!`.
-- This avoids `Fin` index proof complexity.
def isSorted (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: no duplicates in an array, expressed via index inequality.
def arrayNodup (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < arr.size → j < arr.size → i ≠ j → arr[i]! ≠ arr[j]!

-- No preconditions: any integer arrays are allowed.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) Membership in `result` is exactly the symmetric difference of membership in `a` and `b`.
-- 2) `result` has no duplicates.
-- 3) `result` is sorted in nondecreasing order.
-- These properties together uniquely characterize the (canonical) output as the sorted deduplicated
-- list of all elements that appear in exactly one input.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  (∀ (x : Int), x ∈ result ↔ ((x ∈ a ∧ x ∉ b) ∨ (x ∈ b ∧ x ∉ a))) ∧
  arrayNodup result ∧
  isSorted result

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.dissimilarElements_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.dissimilarElements_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.dissimilarElements_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  unfold LLMSpec.precondition VerinaSpec.dissimilarElements_postcond LLMSpec.postcondition; simp +decide ;
  -- Consider the case where `a` contains duplicates.
  use #[1, 1];
  -- Let's choose `b` to be an empty array.
  use #[]; simp +decide [VerinaSpec.inArray] at *; (
  -- Let's choose `result` to be the array `[1, 1]`.
  use #[1, 1]; simp +decide [VerinaSpec.inArray] at *; (
  -- Let's choose any $i$ and $j$ such that $i < j < 2$.
  intro h
  specialize h 0 1
  simp at h))

-/
theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.dissimilarElements_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  sorry

end Proof