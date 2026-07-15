/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8f30c3ef-0060-4484-a89a-c10d7279e266

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (x : Nat) : VerinaSpec.onlineMax_precond a x ↔ LLMSpec.precondition a x

The following was negated by Aristotle:

- theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) : LLMSpec.precondition a x →
  (VerinaSpec.onlineMax_postcond a x result ↔ LLMSpec.postcondition a x result)

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

def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x > 0 ∧ x < a.size

-- x must be at least 1 (as stated in description)

def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: m is the maximum value among indices [0, x).
def isMaxOfPrefix (a : Array Int) (x : Nat) (m : Int) : Prop :=
  (∀ (i : Nat), i < x → a[i]! ≤ m) ∧
  (∃ (i : Nat), i < x ∧ a[i]! = m)

-- Helper predicate: p is the correct index in [x, a.size) according to the problem statement.
def isChosenIndex (a : Array Int) (x : Nat) (m : Int) (p : Nat) : Prop :=
  x ≤ p ∧ p < a.size ∧
  ((∃ (i : Nat), x ≤ i ∧ i < a.size ∧ a[i]! > m) →
      (a[p]! > m ∧ (∀ (j : Nat), x ≤ j ∧ j < p → a[j]! ≤ m))) ∧
  ((¬ ∃ (i : Nat), x ≤ i ∧ i < a.size ∧ a[i]! > m) →
      (p = a.size - 1 ∧ (∀ (i : Nat), x ≤ i ∧ i < a.size → a[i]! ≤ m)))

-- Preconditions from the problem statement.
def precondition (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ 1 ≤ x ∧ x < a.size

-- Postcondition: result = (m, p) where m is max of prefix and p is chosen as specified.
def postcondition (a : Array Int) (x : Nat) (result : Int × Nat) : Prop :=
  isMaxOfPrefix a x result.1 ∧
  isChosenIndex a x result.1 result.2

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (x : Nat) : VerinaSpec.onlineMax_precond a x ↔ LLMSpec.precondition a x := by
  -- The two preconditions are equivalent because they both require the array's size to be positive, x to be at least 1, and x to be less than the array's size.
  simp [VerinaSpec.onlineMax_precond, LLMSpec.precondition];
  -- Since x is a natural number, 0 < x is equivalent to 1 ≤ x.
  intro h_pos h_lt
  apply Iff.intro (fun h => by linarith) (fun h => by linarith)

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) : LLMSpec.precondition a x →
  (VerinaSpec.onlineMax_postcond a x result ↔ LLMSpec.postcondition a x result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the array $a = [1, 2, 3, 4, 5]$ and $x = 3$.
  use #[1, 2, 3, 4, 5], 3;
  -- Let's simplify the goal.
  simp [VerinaSpec.onlineMax_postcond, LLMSpec.postcondition];
  constructor;
  · exact ⟨ by decide, by decide, by decide ⟩;
  · use 3, 4; simp +decide [ LLMSpec.isMaxOfPrefix, LLMSpec.isChosenIndex ] ;

-/
theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) : LLMSpec.precondition a x →
  (VerinaSpec.onlineMax_postcond a x result ↔ LLMSpec.postcondition a x result) := by
  sorry

end Proof