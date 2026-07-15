/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b6e06dc9-ff5e-4b99-8cf5-49909aa3e7c1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (n : Nat) (result : Int × Float) : LLMSpec.precondition n →
  (VerinaSpec.sumAndAverage_postcond n result ↔ LLMSpec.postcondition n result)

The following was negated by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.sumAndAverage_precond n ↔ LLMSpec.precondition n

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

def sumAndAverage_precond (n : Nat) : Prop :=
  n > 0 ∧ n < 9007199254740992

-- n must be positive and bounded for Float precision

def sumAndAverage_postcond (n : Nat) (result: Int × Float) :=
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))

end VerinaSpec

namespace LLMSpec

-- 2^53, the largest integer such that all naturals below it are exactly representable in IEEE-754 Float.
def twoPow53 : Nat := 9007199254740992

-- Closed-form sum S = 1 + 2 + ... + n.
-- Note: This is a mathematical characterization; it is not an algorithmic summation.
def sumOneTo (n : Nat) : Nat := n * (n + 1) / 2

def precondition (n : Nat) : Prop :=
  n > 0 ∧
  n < twoPow53 ∧
  sumOneTo n < twoPow53

def postcondition (n : Nat) (result : Int × Float) : Prop :=
  result.1 = Int.ofNat (sumOneTo n) ∧
  result.2 == (Float.ofInt result.1 / Float.ofNat n)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (n : Nat) : VerinaSpec.sumAndAverage_precond n ↔ LLMSpec.precondition n := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- We'll use that 9007199254740991 is the largest integer such that all naturals below it are exactly representable in IEEE-754 Float.
  use 9007199254740991; simp [VerinaSpec.sumAndAverage_precond, LLMSpec.precondition];
  -- We'll use that 9007199254740991 is the largest integer such that all naturals below it are exactly representable in IEEE-754 Float. Hence, we have:
  norm_cast at *

-/
theorem precondition_equiv (n : Nat) : VerinaSpec.sumAndAverage_precond n ↔ LLMSpec.precondition n := by
  sorry

theorem postcondition_equiv (n : Nat) (result : Int × Float) : LLMSpec.precondition n →
  (VerinaSpec.sumAndAverage_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- By definition of sumAndAverage_postcond and postcondition, we can split into cases based on whether n is zero or positive.
  intro h_pre
  cases' n with n hn;
  · cases h_pre ; contradiction;
  · -- Since the sum and average are the same in both postconditions, the equivalence holds.
    simp [VerinaSpec.sumAndAverage_postcond, LLMSpec.postcondition];
    -- Since the sum and average are the same in both postconditions, the equivalence holds by definition.
    simp [LLMSpec.sumOneTo] at *;
    -- Since the sum is an integer, converting it to an integer (Int.ofNat) and then dividing by (n+1) (which is also an integer) should give the same result as converting the sum to a float (Float.ofNat) and then dividing by (n+1) (Float.ofNat).
    intro h_sum
    simp [h_sum, Float.ofInt, Float.ofNat];
    norm_cast

end Proof