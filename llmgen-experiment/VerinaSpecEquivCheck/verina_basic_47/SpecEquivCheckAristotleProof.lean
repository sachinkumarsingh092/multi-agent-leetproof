/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f31401a5-4153-4d6e-be2f-8c382d150069

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.arraySum_postcond a result ↔ LLMSpec.postcondition a result)

The following was negated by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.arraySum_precond a ↔ LLMSpec.precondition a

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

def arraySum_precond (a : Array Int) : Prop :=
  a.size > 0

def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!

def arraySum_postcond (a : Array Int) (result: Int) :=
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size

end VerinaSpec

namespace LLMSpec

-- Helper definition: the mathematical sum of an array over its index range.
-- This is an observational spec (sum over indices), not an implementation algorithm.
def arrayIndexSum (a : Array Int) : Int :=
  (Finset.range a.size).sum (fun (i : Nat) => a[i]!)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Int) : Prop :=
  result = arrayIndexSum a

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (a : Array Int) : VerinaSpec.arraySum_precond a ↔ LLMSpec.precondition a := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any array `a` with size 0.
  use #[]; simp [VerinaSpec.arraySum_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (a : Array Int) : VerinaSpec.arraySum_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.arraySum_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- Since the precondition is trivially true, we focus on the equivalence of the postconditions.
  simp [VerinaSpec.arraySum_postcond, LLMSpec.postcondition];
  -- By definition of `sumTo`, we know that `sumTo a a.size` is the sum of the elements in the array `a` up to index `a.size`.
  have h_sumTo : VerinaSpec.sumTo a a.size = LLMSpec.arrayIndexSum a := by
    unfold LLMSpec.arrayIndexSum VerinaSpec.sumTo; induction a.size <;> simp_all +decide [ Finset.sum_range_succ ] ;
    unfold VerinaSpec.sumTo; aesop;
  grind +ring

end Proof