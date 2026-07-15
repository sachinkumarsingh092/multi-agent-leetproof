/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1395ab66-1cb4-46eb-9107-dc543f7181af

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.maxArray_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.maxArray_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def maxArray_precond (a : Array Int) : Prop :=
  a.size > 0

def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current

def maxArray_postcond (a : Array Int) (result: Int) :=
  (∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: `val` occurs in the array at some valid index.
-- Using an index-based formulation keeps the spec decidable and avoids list conversions.
def occursIn (a : Array Int) (val : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = val

-- Preconditions
-- The array must be non-empty.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result is a maximum element: (1) it is an element of the array,
-- and (2) all elements are ≤ result.
def postcondition (a : Array Int) (result : Int) : Prop :=
  occursIn a result ∧
  (∀ (i : Nat), i < a.size → a[i]! ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.maxArray_precond a ↔ LLMSpec.precondition a := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.maxArray_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.maxArray_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- By definition of `maxArray_precond` and `precondition`, we know that `a.size > 0`.
  intro h_precond
  constructor;
  · -- If the result is the maximum element in the array, then it must be greater than or equal to all elements in the array.
    intro h_max
    have h_ge : ∀ i, i < a.size → a[i]! ≤ result := by
      exact fun i hi => h_max.1 i hi;
    exact ⟨ h_max.2.choose_spec.2 ▸ ⟨ h_max.2.choose, h_max.2.choose_spec.1, rfl ⟩, h_ge ⟩;
  · rintro ⟨ ⟨ i, hi, rfl ⟩, h ⟩;
    exact ⟨ h, i, hi, rfl ⟩

end Proof