/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 00e532d6-7f5a-41d7-be4e-95be227bdb0f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (j : Nat) : VerinaSpec.TestArrayElements_precond a j ↔ LLMSpec.precondition a j

The following was negated by Aristotle:

- theorem postcondition_equiv (a : Array Int) (j : Nat) (result : Array Int) : LLMSpec.precondition a j →
  (VerinaSpec.TestArrayElements_postcond a j result ↔ LLMSpec.postcondition a j result)

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

def TestArrayElements_precond (a : Array Int) (j : Nat) : Prop :=
  j < a.size

def TestArrayElements_postcond (a : Array Int) (j : Nat) (result: Array Int) :=
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)

end VerinaSpec

namespace LLMSpec

-- Precondition: the update index must be in bounds.
-- Note: The constraint 0 ≤ j is automatic since j : Nat.
def precondition (a : Array Int) (j : Nat) : Prop :=
  j < a.size

-- Postcondition: same size; pointwise update semantics.
def postcondition (a : Array Int) (j : Nat) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = (if i = j then (60 : Int) else a[i]!))

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (j : Nat) : VerinaSpec.TestArrayElements_precond a j ↔ LLMSpec.precondition a j := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.TestArrayElements_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (a : Array Int) (j : Nat) (result : Array Int) : LLMSpec.precondition a j →
  (VerinaSpec.TestArrayElements_postcond a j result ↔ LLMSpec.postcondition a j result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider an array `a` with size 1 and an index `j` such that `j = 0`.
  use #[10], 0;
  -- Let's choose the result array to be `[60, 10]`.
  use #[60, 10];
  -- Let's simplify the goal.
  simp +decide [VerinaSpec.TestArrayElements_postcond, LLMSpec.postcondition];
  -- The size of the array is 1, so 0 is less than 1.
  simp [LLMSpec.precondition]

-/
theorem postcondition_equiv (a : Array Int) (j : Nat) (result : Array Int) : LLMSpec.precondition a j →
  (VerinaSpec.TestArrayElements_postcond a j result ↔ LLMSpec.postcondition a j result) := by
  sorry

end Proof