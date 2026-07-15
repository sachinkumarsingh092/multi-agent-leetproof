/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 95b8c69c-8c01-4268-9baa-35cfdc3f4292

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (n : Int) (a : Array Int) (result : Bool) : LLMSpec.precondition n a →
  (VerinaSpec.isGreater_postcond n a result ↔ LLMSpec.postcondition n a result)

The following was negated by Aristotle:

- theorem precondition_equiv (n : Int) (a : Array Int) : VerinaSpec.isGreater_precond n a ↔ LLMSpec.precondition n a

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

def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  a.size > 0

def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) :=
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result

end VerinaSpec

namespace LLMSpec

-- Helper predicate: n is strictly greater than all elements of a.
def GreaterThanAllProp (n : Int) (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! < n

def precondition (n : Int) (a : Array Int) : Prop :=
  True

def postcondition (n : Int) (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ GreaterThanAllProp n a)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (n : Int) (a : Array Int) : VerinaSpec.isGreater_precond n a ↔ LLMSpec.precondition n a := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- By definition of `precondition`, we know that `precondition n a` is true if and only if `n` is greater than all elements of `a`.
  simp [VerinaSpec.isGreater_precond, LLMSpec.precondition] at *

-/
theorem precondition_equiv (n : Int) (a : Array Int) : VerinaSpec.isGreater_precond n a ↔ LLMSpec.precondition n a := by
  sorry

theorem postcondition_equiv (n : Int) (a : Array Int) (result : Bool) : LLMSpec.precondition n a →
  (VerinaSpec.isGreater_postcond n a result ↔ LLMSpec.postcondition n a result) := by
  -- The postcondition for `isGreater` is equivalent to the postcondition for `GreaterThanAllProp` because they both state that `n` is greater than all elements in `a`.
  simp [VerinaSpec.isGreater_postcond, LLMSpec.postcondition, LLMSpec.GreaterThanAllProp];
  cases a ; aesop

end Proof