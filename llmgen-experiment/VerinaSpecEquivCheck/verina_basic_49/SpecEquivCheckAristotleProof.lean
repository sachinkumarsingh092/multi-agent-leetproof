/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 764d0217-70a6-437e-81cc-447e1df56eb1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (a : Array Int) (result : Option Nat) : LLMSpec.precondition a →
  (VerinaSpec.findFirstOdd_postcond a result ↔ LLMSpec.postcondition a result)

The following was negated by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.findFirstOdd_precond a ↔ LLMSpec.precondition a

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

def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0

def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0

def findFirstOdd_postcond (a : Array Int) (result: Option Nat) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)

end VerinaSpec

namespace LLMSpec

-- Helper: oddness predicate for Int (avoids relying on `Int.Odd`, which may not be available)
def isOddInt (x : Int) : Prop := x % 2 ≠ 0

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Option Nat) : Prop :=
  match result with
  | none =>
      ∀ (i : Nat), i < a.size → ¬ isOddInt (a[i]!)
  | some k =>
      k < a.size ∧
      isOddInt (a[k]!) ∧
      ∀ (j : Nat), j < k → ¬ isOddInt (a[j]!)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (a : Array Int) : VerinaSpec.findFirstOdd_precond a ↔ LLMSpec.precondition a := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the empty array.
  use #[]
  simp [VerinaSpec.findFirstOdd_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (a : Array Int) : VerinaSpec.findFirstOdd_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Option Nat) : LLMSpec.precondition a →
  (VerinaSpec.findFirstOdd_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- By definition of `isOdd`, we know that `isOdd x` is equivalent to `x % 2 ≠ 0`.
  have h_isOdd : ∀ x : ℤ, VerinaSpec.isOdd x ↔ LLMSpec.isOddInt x := by
    -- By definition of `isOdd`, we know that `isOdd x` is equivalent to `x % 2 ≠ 0` for any integer `x`.
    simp [VerinaSpec.isOdd, LLMSpec.isOddInt];
  -- By substituting `h_isOdd` into the postconditions, we can see that they are indeed equivalent.
  simp [LLMSpec.precondition, VerinaSpec.findFirstOdd_postcond, LLMSpec.postcondition, h_isOdd];
  -- Since the match expression is symmetric, the equivalence holds.
  cases result <;> simp [h_isOdd]

end Proof