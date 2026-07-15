/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8ab6c5c1-dcd7-429b-b254-e8c1864e6477

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : VerinaSpec.modify_array_element_precond arr index1 index2 val ↔ LLMSpec.precondition arr index1 index2 val

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result : Array (Array Nat)) : LLMSpec.precondition arr index1 index2 val →
  (VerinaSpec.modify_array_element_postcond arr index1 index2 val result ↔ LLMSpec.postcondition arr index1 index2 val result)

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

def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size

def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val

def modify_array_element_postcond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result: Array (Array Nat)) :=
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)

end VerinaSpec

namespace LLMSpec

-- Preconditions: indices are in bounds.
-- This captures the problem statement assumption that both indices are valid.
-- The bounds also ensure all array indexing used in the postcondition is safe.
def precondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size

-- Postcondition: outer size preserved; only the selected cell (index1,index2) is updated.
-- All other inner arrays are identical; in the modified inner array, all other positions are identical.
def postcondition (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat)
    (result : Array (Array Nat)) : Prop :=
  result.size = arr.size ∧
  (∀ (i : Nat), i < arr.size →
    (if _h1 : i = index1 then
        let a : Array Nat := arr[i]!
        let r : Array Nat := result[i]!
        r.size = a.size ∧
        (∀ (j : Nat), j < a.size →
          (if _h2 : j = index2 then
              r[j]! = val
            else
              r[j]! = a[j]!))
      else
        result[i]! = arr[i]!))

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : VerinaSpec.modify_array_element_precond arr index1 index2 val ↔ LLMSpec.precondition arr index1 index2 val := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.modify_array_element_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result : Array (Array Nat)) : LLMSpec.precondition arr index1 index2 val →
  (VerinaSpec.modify_array_element_postcond arr index1 index2 val result ↔ LLMSpec.postcondition arr index1 index2 val result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any array `arr` with dimensions 2x2.
  use #[#[0, 0], #[0, 0]];
  -- Choose `index1 = 0`, `index2 = 0`, and `val = 1`.
  use 0, 0, 1;
  -- Let's choose the result array to be #[#[1], #[0, 0]].
  use #[#[1], #[0, 0]];
  -- Let's simplify the goal.
  simp +decide [LLMSpec.precondition, LLMSpec.postcondition, VerinaSpec.modify_array_element_postcond]

-/
theorem postcondition_equiv (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result : Array (Array Nat)) : LLMSpec.precondition arr index1 index2 val →
  (VerinaSpec.modify_array_element_postcond arr index1 index2 val result ↔ LLMSpec.postcondition arr index1 index2 val result) := by
  sorry

end Proof