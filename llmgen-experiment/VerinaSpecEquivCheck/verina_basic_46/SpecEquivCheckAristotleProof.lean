/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 55209e2e-ce2a-4dd2-ba6d-6d502fc31cc6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (elem : Int) : VerinaSpec.lastPosition_precond arr elem ↔ LLMSpec.precondition arr elem

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) : LLMSpec.precondition arr elem →
  (VerinaSpec.lastPosition_postcond arr elem result ↔ LLMSpec.postcondition arr elem result)

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

def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))

end VerinaSpec

namespace LLMSpec

-- Helper: sortedness in non-decreasing order (using Nat indices and `arr[i]!`).
def isSortedNondesc (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: element membership expressed via indices.
def contains (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: `k` is a last-occurrence index of `elem`.
def isLastOccurrenceIdx (arr : Array Int) (elem : Int) (k : Nat) : Prop :=
  k < arr.size ∧
  arr[k]! = elem ∧
  ∀ (j : Nat), k < j → j < arr.size → arr[j]! ≠ elem

-- Preconditions: the input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (elem : Int) : Prop :=
  isSortedNondesc arr

-- Postconditions: result is -1 iff `elem` is absent, otherwise result is the (unique) last index.
def postcondition (arr : Array Int) (elem : Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ (i : Nat), i < arr.size → arr[i]! ≠ elem)) ∨
  (∃ (k : Nat), result = Int.ofNat k ∧ isLastOccurrenceIdx arr elem k)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (elem : Int) : VerinaSpec.lastPosition_precond arr elem ↔ LLMSpec.precondition arr elem := by
  -- The two preconditions are equivalent because they both describe the same property of the array being sorted in non-decreasing order.
  apply Iff.intro;
  · intro h i j hij hj;
    have := List.pairwise_iff_get.mp h;
    convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
    · grind;
    · grind;
  · intro h;
    refine' List.pairwise_iff_get.mpr _;
    -- By definition of `isSortedNondesc`, we know that for any `i` and `j` in the list, if `i < j`, then `arr[i]! ≤ arr[j]!`.
    intros i j hij
    have := h i j hij
    aesop

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) : LLMSpec.precondition arr elem →
  (VerinaSpec.lastPosition_postcond arr elem result ↔ LLMSpec.postcondition arr elem result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  fconstructor;
  exact #[ 0 ];
  use 0; simp +decide [ LLMSpec.precondition ] ;
  constructor;
  · exact fun i j hij _ => by rcases i with ( _ | _ | i ) <;> rcases j with ( _ | _ | j ) <;> trivial;
  · use -2; simp +decide [ VerinaSpec.lastPosition_postcond, LLMSpec.postcondition ] ;

-/
theorem postcondition_equiv (arr : Array Int) (elem : Int) (result : Int) : LLMSpec.precondition arr elem →
  (VerinaSpec.lastPosition_postcond arr elem result ↔ LLMSpec.postcondition arr elem result) := by
  sorry

end Proof