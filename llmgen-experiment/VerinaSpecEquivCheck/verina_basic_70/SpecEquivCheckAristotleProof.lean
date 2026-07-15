/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3f1323e9-0c8f-4ddd-bbca-b94dbd14e87e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (P : Int -> Bool) : VerinaSpec.LinearSearch3_precond a P ↔ LLMSpec.precondition a P

- theorem postcondition_equiv (a : Array Int) (P : Int -> Bool) (result : Nat) : LLMSpec.precondition a P →
  (VerinaSpec.LinearSearch3_postcond a P result ↔ LLMSpec.postcondition a P result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  ∃ i, i < a.size ∧ P (a[i]!)

def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) :=
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))

end VerinaSpec

namespace LLMSpec

-- Helper: `P` holds at index `i` (with bounds).
-- This is a Prop, even though `P` returns Bool.
def HoldsAt (a : Array Int) (P : Int → Bool) (i : Nat) : Prop :=
  i < a.size ∧ P (a[i]!) = true

-- Preconditions: there exists at least one index satisfying `P`.
def precondition (a : Array Int) (P : Int → Bool) : Prop :=
  ∃ i : Nat, HoldsAt a P i

-- Postconditions: `result` is the first index satisfying `P`.
def postcondition (a : Array Int) (P : Int → Bool) (result : Nat) : Prop :=
  result < a.size ∧
  P (a[result]!) = true ∧
  (∀ j : Nat, j < result → P (a[j]!) = false)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (P : Int -> Bool) : VerinaSpec.LinearSearch3_precond a P ↔ LLMSpec.precondition a P := by
  -- The preconditions are equivalent because they both state that there exists an index where P holds.
  simp [VerinaSpec.LinearSearch3_precond, LLMSpec.precondition];
  -- The equivalence follows directly from the definition of `HoldsAt`.
  simp [LLMSpec.HoldsAt]

theorem postcondition_equiv (a : Array Int) (P : Int -> Bool) (result : Nat) : LLMSpec.precondition a P →
  (VerinaSpec.LinearSearch3_postcond a P result ↔ LLMSpec.postcondition a P result) := by
  -- By definition of `precondition`, we know that there exists some index `i` such that `P (a[i]!)` holds.
  intro h_pre
  simp [VerinaSpec.LinearSearch3_postcond, LLMSpec.postcondition]

end Proof