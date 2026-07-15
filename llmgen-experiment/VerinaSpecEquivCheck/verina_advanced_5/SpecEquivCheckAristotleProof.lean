/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 80d8a6af-2d85-47c4-8479-dcb5c7e70397

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (l1 : List Nat) (l2 : List Nat) : VerinaSpec.addTwoNumbers_precond l1 l2 ↔ LLMSpec.precondition l1 l2

- theorem postcondition_equiv (l1 : List Nat) (l2 : List Nat) (result : List Nat) : LLMSpec.precondition l1 l2 →
  (VerinaSpec.addTwoNumbers_postcond l1 l2 result ↔ LLMSpec.postcondition l1 l2 result)

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

def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds

def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])

def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) : Prop :=
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10) ∧
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))

end VerinaSpec

namespace LLMSpec

-- A digit list is valid (base 10) iff all elements are < 10.
-- We use strict inequality (< 10) because digits are naturals.
def allDigitsBase10 (l : List Nat) : Prop :=
  ∀ (d : Nat), d ∈ l → d < 10

-- The base-10 value of a little-endian (reversed) digit list.
-- Mathlib's Nat.ofDigits uses the little-endian convention.
def valueBase10LE (l : List Nat) : Nat :=
  Nat.ofDigits 10 l

-- Canonicality for a base-10 little-endian digit list:
-- it is non-empty, all digits are valid, and it has no unnecessary most-significant zeros.
-- We treat 0 specially: the unique canonical representation is [0].
def canonicalBase10LE (l : List Nat) : Prop :=
  l ≠ [] ∧
  allDigitsBase10 l ∧
  ((valueBase10LE l = 0) ↔ (l = [0])) ∧
  (valueBase10LE l ≠ 0 → l.getLast? ≠ some 0)

-- Inputs are required to be non-empty and contain only decimal digits.
-- (We do not require canonical inputs; leading zeros are allowed in the most-significant positions.)
def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1 ≠ [] ∧
  l2 ≠ [] ∧
  allDigitsBase10 l1 ∧
  allDigitsBase10 l2

-- The output must be a canonical base-10 little-endian digit list representing the sum.
def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=
  canonicalBase10LE result ∧
  valueBase10LE result = valueBase10LE l1 + valueBase10LE l2

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (l1 : List Nat) (l2 : List Nat) : VerinaSpec.addTwoNumbers_precond l1 l2 ↔ LLMSpec.precondition l1 l2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where `l1` is `[1, 0]` and `l2` is `[1, 0]`.
  use [1, 0], [1, 0];
  -- Let's simplify the goal.
  simp [VerinaSpec.addTwoNumbers_precond, LLMSpec.precondition];
  -- We need to show that all digits in the list [1, 0] are less than 10.
  intro d hd
  aesop

-/
theorem precondition_equiv (l1 : List Nat) (l2 : List Nat) : VerinaSpec.addTwoNumbers_precond l1 l2 ↔ LLMSpec.precondition l1 l2 := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The function `VerinaSpec.listToNat` is equivalent to `LLMSpec.valueBase10LE` (which wraps `Nat.ofDigits 10`).
-/
lemma listToNat_eq_valueBase10LE (l : List Nat) : VerinaSpec.listToNat l = LLMSpec.valueBase10LE l := by
  unfold LLMSpec.valueBase10LE VerinaSpec.listToNat; induction l <;> simp +arith +decide [ *, Nat.ofDigits ] ;
  cases ‹List ℕ› <;> aesop

/-
There exists a counterexample to the equivalence of the postconditions. Specifically, when `l1 = [0, 0]`, `l2 = [0]`, and `result = [0]`, the LLM spec is satisfied but the Verina spec is not.
-/
lemma postcondition_equiv_counterexample : ∃ l1 l2 result,
  LLMSpec.precondition l1 l2 ∧
  ¬(VerinaSpec.addTwoNumbers_postcond l1 l2 result ↔ LLMSpec.postcondition l1 l2 result) := by
    -- Let `l1 = [0, 0]`, `l2 = [0]`, `result = [0]`.
    use [0, 0], [0], [0];
    unfold LLMSpec.precondition LLMSpec.postcondition VerinaSpec.addTwoNumbers_postcond; simp +decide ;
    unfold LLMSpec.allDigitsBase10 LLMSpec.canonicalBase10LE; simp +decide ;
    exact fun d hd => by fin_cases hd; decide;

end AristotleLemmas

theorem postcondition_equiv (l1 : List Nat) (l2 : List Nat) (result : List Nat) : LLMSpec.precondition l1 l2 →
  (VerinaSpec.addTwoNumbers_postcond l1 l2 result ↔ LLMSpec.postcondition l1 l2 result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the counterexample where `l1 = [0, 0]`, `l2 = [0]`, and `result = [0]`.
  use [0, 0], [0], [0];
  -- We need to show that the counterexample satisfies the LLM spec but not the Verina spec.
  simp [LLMSpec.precondition, LLMSpec.postcondition, VerinaSpec.addTwoNumbers_postcond];
  -- Let's simplify the goal.
  simp [LLMSpec.allDigitsBase10, LLMSpec.canonicalBase10LE, LLMSpec.valueBase10LE];
  -- Let's simplify the goal using the definition of `Nat.ofDigits`.
  simp [Nat.ofDigits]

-/
theorem postcondition_equiv (l1 : List Nat) (l2 : List Nat) (result : List Nat) : LLMSpec.precondition l1 l2 →
  (VerinaSpec.addTwoNumbers_postcond l1 l2 result ↔ LLMSpec.postcondition l1 l2 result) := by
  sorry

end Proof