/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 43be526a-fca5-4b0a-9894-4641d0a82567

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (numbers : List Float) (threshold : Float) : VerinaSpec.has_close_elements_precond numbers threshold ↔ LLMSpec.precondition numbers threshold

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

def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b

def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  threshold ≥ 0.0 ∧
  ¬threshold.isNaN ∧
  numbers.all (fun x => ¬x.isNaN ∧ ¬x.isInf)

-- no NaN or Inf values

def has_close_elements_postcond (numbers : List Float) (threshold : Float) (result: Bool) :=
  ¬ result ↔ (List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers)

end VerinaSpec

namespace LLMSpec

-- A Float value is considered valid if it is neither NaN nor infinite.
-- This matches the problem statement assumption and is kept decidable via boolean tests.
def FloatValid (x : Float) : Prop :=
  (x.isNaN = false) ∧ (x.isInf = false)

-- There exists a close pair of distinct indices in the list.
def HasClosePair (numbers : List Float) (threshold : Float) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < numbers.length ∧
    j < numbers.length ∧
    i ≠ j ∧
    Float.abs (numbers[i]! - numbers[j]!) < threshold

-- Preconditions
-- 1) All list elements are valid floats.
-- 2) The threshold is a valid float and is non-negative.
def precondition (numbers : List Float) (threshold : Float) : Prop :=
  (∀ (i : Nat), i < numbers.length → FloatValid (numbers[i]!)) ∧
  FloatValid threshold ∧
  (0.0 ≤ threshold)

-- Postcondition
-- The result is true iff a close pair exists.
def postcondition (numbers : List Float) (threshold : Float) (result : Bool) : Prop :=
  (result = true ↔ HasClosePair numbers threshold)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (numbers : List Float) (threshold : Float) : VerinaSpec.has_close_elements_precond numbers threshold ↔ LLMSpec.precondition numbers threshold := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where the list is empty.
  use [];
  norm_num [ VerinaSpec.has_close_elements_precond, LLMSpec.precondition ];
  -- Consider the case where the threshold is 0.0.
  use Float.ofBits 0x7ff0000000000000;
  -- Let's simplify the goal.
  simp [LLMSpec.FloatValid] at *;
  -- We'll use that 9218868437227405312 is a positive infinity to show that the condition holds.
  skip
  native_decide +revert

-/
theorem precondition_equiv (numbers : List Float) (threshold : Float) : VerinaSpec.has_close_elements_precond numbers threshold ↔ LLMSpec.precondition numbers threshold := by
  sorry

/- Aristotle failed to find a proof. -/
theorem postcondition_equiv (numbers : List Float) (threshold : Float) (result : Bool) : LLMSpec.precondition numbers threshold →
  (VerinaSpec.has_close_elements_postcond numbers threshold result ↔ LLMSpec.postcondition numbers threshold result) := by
  sorry

end Proof