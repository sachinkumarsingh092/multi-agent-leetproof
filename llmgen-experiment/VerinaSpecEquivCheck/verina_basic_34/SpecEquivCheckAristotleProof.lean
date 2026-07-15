/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6e2ad42e-a675-4ff3-8a70-adcb85d4b675

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) : VerinaSpec.findEvenNumbers_precond arr ↔ LLMSpec.precondition arr

The following was negated by Aristotle:

- theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.findEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result)

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

def isEven (n : Int) : Bool :=
  n % 2 = 0

def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: evenness for Int.
-- We keep it as a Prop; we avoid needing decidability by never branching (`if`) on it in specs.
def EvenInt (x : Int) : Prop := x % 2 = 0

-- Order preservation: `result` is obtained by selecting elements from `arr` at strictly increasing indices.
-- This expresses that `result` is a subsequence of `arr` (with multiplicity), and preserves order.
def isOrderPreservingSelection (arr : Array Int) (result : Array Int) : Prop :=
  ∃ f : Nat → Nat,
    (∀ i : Nat, i < result.size → f i < arr.size ∧ result[i]! = arr[f i]!) ∧
    (∀ i : Nat, ∀ j : Nat, i < j → j < result.size → f i < f j)

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) Every element in `result` is even.
-- 2) For each integer value x:
--    - if x is even, its multiplicity is preserved (same count as in `arr`)
--    - if x is odd, it does not appear in `result` (count = 0)
-- 3) The relative order of the kept elements matches their order in `arr`.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  (∀ i : Nat, i < result.size → EvenInt (result[i]!)) ∧
  (∀ x : Int, EvenInt x → result.count x = arr.count x) ∧
  (∀ x : Int, ¬ EvenInt x → result.count x = 0) ∧
  isOrderPreservingSelection arr result

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) : VerinaSpec.findEvenNumbers_precond arr ↔ LLMSpec.precondition arr := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.findEvenNumbers_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.findEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  unfold VerinaSpec.findEvenNumbers_postcond LLMSpec.postcondition;
  use #[ 2, 2 ] ; simp +decide ;
  -- Let's choose any `x` that satisfies the conditions.
  use by
    -- The precondition is trivially true for any array.
    simp [LLMSpec.precondition]
  use #[2]
  simp +decide [LLMSpec.EvenInt];
  -- Let's choose any `x` that satisfies the conditions and derive a contradiction.
  intro h1 h2 h3
  specialize h1 2
  simp at h1

-/
theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.findEvenNumbers_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  sorry

end Proof