/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 28184a83-f3d9-4e09-b1bd-3b6408c66a48

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (target : Int) : VerinaSpec.findFirstOccurrence_precond arr target ↔ LLMSpec.precondition arr target

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) : LLMSpec.precondition arr target →
  (VerinaSpec.findFirstOccurrence_postcond arr target result ↔ LLMSpec.postcondition arr target result)

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

def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) :=
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))

end VerinaSpec

namespace LLMSpec

-- Array is sorted in non-decreasing order.
-- We phrase this using Nat indices and `arr[i]!` with explicit bounds.
def isSortedND (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: the input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedND arr

-- Postcondition:
-- Either the target is absent and we return -1,
-- or we return `Int.ofNat k` where `k` is the smallest index with `arr[k] = target`.
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ (i : Nat), i < arr.size → arr[i]! ≠ target)) ∨
  (∃ (k : Nat),
      k < arr.size ∧
      result = Int.ofNat k ∧
      arr[k]! = target ∧
      (∀ (j : Nat), j < k → arr[j]! ≠ target))

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (target : Int) : VerinaSpec.findFirstOccurrence_precond arr target ↔ LLMSpec.precondition arr target := by
  -- The two preconditions are equivalent because they both describe the same condition: the array is sorted in non-decreasing order.
  apply Iff.intro;
  · intro h i j hij hlt
    have h_eq : arr.toList.Pairwise (· ≤ ·) := by
      exact h
    have h_le : arr[i]! ≤ arr[j]! := by
      rw [ List.pairwise_iff_get ] at h_eq;
      convert h_eq ⟨ i, by simpa using hij.trans hlt ⟩ ⟨ j, by simpa using hlt ⟩ hij using 1 <;> simp +decide [ Array.get ];
      · exact?;
      · grind
    exact h_le;
  · intro h_sorted
    apply List.pairwise_iff_get.mpr;
    -- By definition of `toList`, we know that `arr.toList.get i = arr[i]!` for any `i`. Therefore, we can apply the hypothesis `h_sorted` to conclude the proof.
    intros i j hij
    have := h_sorted i j hij
    aesop

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) : LLMSpec.precondition arr target →
  (VerinaSpec.findFirstOccurrence_postcond arr target result ↔ LLMSpec.postcondition arr target result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where the array is empty.
  use #[];
  -- In this case, the array is empty, so the target cannot be found.
  use 0, 0
  simp [LLMSpec.precondition, LLMSpec.postcondition, VerinaSpec.findFirstOccurrence_postcond];
  -- The empty array is trivially sorted.
  simp [LLMSpec.isSortedND]

-/
theorem postcondition_equiv (arr : Array Int) (target : Int) (result : Int) : LLMSpec.precondition arr target →
  (VerinaSpec.findFirstOccurrence_postcond arr target result ↔ LLMSpec.postcondition arr target result) := by
  sorry

end Proof