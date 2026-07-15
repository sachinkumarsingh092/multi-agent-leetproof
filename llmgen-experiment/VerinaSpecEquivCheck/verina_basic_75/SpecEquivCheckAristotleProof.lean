/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dbcbfb0c-c930-4231-9afc-6b367416eaf4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.minArray_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.minArray_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def minArray_precond (a : Array Int) : Prop :=
  a.size > 0

def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin

def minArray_postcond (a : Array Int) (result: Int) :=
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)

end VerinaSpec

namespace LLMSpec

-- Precondition: the array is non-empty.
-- We keep this decidable/computable by using `a.size > 0`.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: `result` is a minimum element of `a`.
-- 1) Lower bound: result ≤ every element in the array.
-- 2) Attainment: result equals some element in the array.
def postcondition (a : Array Int) (result : Int) : Prop :=
  (∀ (i : Nat), i < a.size → result ≤ a[i]!) ∧
  (∃ (i : Nat), i < a.size ∧ result = a[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.minArray_precond a ↔ LLMSpec.precondition a := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.minArray_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.minArray_postcond a result ↔ LLMSpec.postcondition a result) := by
  exact?

end Proof