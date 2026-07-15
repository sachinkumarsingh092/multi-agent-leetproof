/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8d611530-1670-48aa-8a04-859f0c2287d3

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.minimumRightShifts_postcond nums result ↔ LLMSpec.postcondition nums result)

The following was negated by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.minimumRightShifts_precond nums ↔ LLMSpec.precondition nums

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

def minimumRightShifts_precond (nums : List Int) : Prop :=
  List.Nodup nums

def minimumRightShifts_postcond (nums : List Int) (result: Int) : Prop :=
  let n := nums.length
  let isSorted (l : List Int) := List.Pairwise (· ≤ ·) l
  let rightShift (k : Nat) (l : List Int) := l.rotateRight k
  if n <= 1 then result = 0 else -- specification for base cases
  (result ≥ 0 ∧
   result < n ∧
   isSorted (rightShift result.toNat nums) ∧
   (List.range result.toNat |>.all (fun j => ¬ isSorted (rightShift j nums)))
  ) ∨
  (result = -1 ∧
   (List.range n |>.all (fun k => ¬ isSorted (rightShift k nums)))
  )

end VerinaSpec

namespace LLMSpec

-- A computable notion of ascending sortedness (using Mathlib's `List.Sorted`).
def isSortedAsc (l : List Int) : Prop :=
  l.Sorted (· ≤ ·)

-- Right shift by k: implemented as a left-rotation by (len - (k mod len)).
-- For empty lists, a shift leaves the list unchanged.
def rightShift (l : List Int) (k : Nat) : List Int :=
  if h : l.length = 0 then
    l
  else
    let n := l.length
    l.rotate (n - (k % n))

-- Preconditions from the problem statement: distinct, positive integers.
def precondition (nums : List Int) : Prop :=
  nums.Nodup ∧ ∀ (x : Int), x ∈ nums → 0 < x

-- Postcondition: either result = -1 and no right shift sorts the list,
-- or result is a nonnegative integer representing the minimum right-shift count that sorts it.
def postcondition (nums : List Int) (result : Int) : Prop :=
  (result = -1 ∧
    (nums.length = 0 → False) ∧
    (∀ (k : Nat), k < nums.length → ¬ isSortedAsc (rightShift nums k)))
  ∨
  (0 ≤ result ∧
    (nums.length = 0 → result = 0) ∧
    (nums.length > 0 → result.toNat < nums.length) ∧
    isSortedAsc (rightShift nums result.toNat) ∧
    (∀ (k : Nat), k < result.toNat → ¬ isSortedAsc (rightShift nums k)))

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (nums : List Int) : VerinaSpec.minimumRightShifts_precond nums ↔ LLMSpec.precondition nums := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the list `[0]`. This list has no duplicates, but it does not satisfy the condition that all elements are positive.
  use [0]
  simp [VerinaSpec.minimumRightShifts_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (nums : List Int) : VerinaSpec.minimumRightShifts_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.minimumRightShifts_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold LLMSpec.precondition LLMSpec.postcondition VerinaSpec.minimumRightShifts_postcond;
  -- Let's split into cases based on the length of the list.
  by_cases h_len : nums.length ≤ 1;
  · rcases nums with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
    · unfold LLMSpec.isSortedAsc LLMSpec.rightShift; aesop;
    · -- Since the list has only one element, the right shift by 0 is just the list itself, which is trivially sorted.
      simp [LLMSpec.rightShift, LLMSpec.isSortedAsc];
      grind;
  · -- By definition of `rightShift`, we know that rotating by `k` positions is equivalent to rotating by `n - (k % n)` positions.
    have h_rightShift_eq : ∀ k : ℕ, List.rotateRight nums k = List.rotate nums (nums.length - (k % nums.length)) := by
      intro k
      simp [List.rotateRight];
      rw [ List.rotate_eq_drop_append_take ] ; aesop;
      exact Nat.sub_le _ _;
    unfold LLMSpec.rightShift LLMSpec.isSortedAsc; simp_all +decide [ List.range_succ_eq_map ] ;
    split_ifs <;> simp_all +decide [ List.Sorted ];
    · linarith;
    · grind +ring

end Proof