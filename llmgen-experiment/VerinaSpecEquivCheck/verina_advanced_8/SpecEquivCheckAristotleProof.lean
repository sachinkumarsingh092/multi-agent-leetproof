/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 38c3560f-e264-4ddf-9d18-5838f5b47969

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (gas : List Int) (cost : List Int) : VerinaSpec.canCompleteCircuit_precond gas cost ↔ LLMSpec.precondition gas cost

The following was negated by Aristotle:

- theorem postcondition_equiv (gas : List Int) (cost : List Int) (result : Int) : LLMSpec.precondition gas cost →
  (VerinaSpec.canCompleteCircuit_postcond gas cost result ↔ LLMSpec.postcondition gas cost result)

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

def canCompleteCircuit_precond (gas : List Int) (cost : List Int) : Prop :=
  gas.length > 0 ∧ gas.length = cost.length

def canCompleteCircuit_postcond (gas : List Int) (cost : List Int) (result: Int) : Prop :=
  let valid (start : Nat) := List.range gas.length |>.all (fun i =>
    let acc := List.range (i + 1) |>.foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)
  (result = -1 → (List.range gas.length).all (fun start => ¬ valid start)) ∧
  (result ≥ 0 → result < gas.length ∧ valid result.toNat ∧ (List.range result.toNat).all (fun start => ¬ valid start))

end VerinaSpec

namespace LLMSpec

-- Helper: integer sum of a list.
-- We use `foldl` because it is a standard Mathlib/List operation.
def sumIntList (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc + x) 0

-- Helper: circular index; meaningful when `n > 0`.
def circIdx (n : Nat) (i : Nat) : Nat :=
  i % n

-- Helper: net gain at (circular) station index `i`.
def circDiff (gas : List Int) (cost : List Int) (i : Nat) : Int :=
  let n : Nat := gas.length
  let j : Nat := circIdx n i
  gas[j]! - cost[j]!

-- Helper: balance after taking exactly `t` steps starting from `start`.
-- This is a mathematical finite sum over the range `{0,1,...,t-1}`.
def balanceFrom (gas : List Int) (cost : List Int) (start : Nat) (t : Nat) : Int :=
  (Finset.range t).sum (fun k => circDiff gas cost (start + k))

-- Helper: a start index is valid if all prefix balances along the `n` steps are nonnegative.
def validStart (gas : List Int) (cost : List Int) (start : Nat) : Prop :=
  let n : Nat := gas.length
  start < n ∧
    (∀ t : Nat, t ≤ n → 0 ≤ balanceFrom gas cost start t)

-- Helper: existence of some valid start.
def existsValidStart (gas : List Int) (cost : List Int) : Prop :=
  let n : Nat := gas.length
  ∃ s : Nat, s < n ∧ validStart gas cost s

-- Preconditions: lists have equal non-zero length.
def precondition (gas : List Int) (cost : List Int) : Prop :=
  gas.length = cost.length ∧ gas.length > 0

-- Postcondition:
-- * If no valid start exists, result is `-1`.
-- * Otherwise, result is a valid start index (as a nonnegative Int within range)
--   and is minimal among all valid starts.
def postcondition (gas : List Int) (cost : List Int) (result : Int) : Prop :=
  let n : Nat := gas.length
  (result = (-1) ↔ ¬ existsValidStart gas cost) ∧
  (result ≠ (-1) →
      0 ≤ result ∧
      result.toNat < n ∧
      validStart gas cost result.toNat ∧
      (∀ s : Nat, s < n → validStart gas cost s → result.toNat ≤ s))

end LLMSpec

section Proof

theorem precondition_equiv (gas : List Int) (cost : List Int) : VerinaSpec.canCompleteCircuit_precond gas cost ↔ LLMSpec.precondition gas cost := by
  -- The equivalence follows from the commutativity of conjunction.
  apply Iff.intro (fun h => ⟨h.right, h.left⟩) (fun h => ⟨h.right, h.left⟩)

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (gas : List Int) (cost : List Int) (result : Int) : LLMSpec.precondition gas cost →
  (VerinaSpec.canCompleteCircuit_postcond gas cost result ↔ LLMSpec.postcondition gas cost result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose specific values for `gas` and `cost` that satisfy the precondition.
  use [1, 2, 3], [3, 2, 1];
  -- Let's simplify the goal.
  simp +decide [VerinaSpec.canCompleteCircuit_postcond, LLMSpec.postcondition];
  constructor;
  · exact ⟨ rfl, by decide ⟩;
  · use -2; simp +decide ;

-/
theorem postcondition_equiv (gas : List Int) (cost : List Int) (result : Int) : LLMSpec.precondition gas cost →
  (VerinaSpec.canCompleteCircuit_postcond gas cost result ↔ LLMSpec.postcondition gas cost result) := by
  sorry

end Proof