/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 44e61994-3ef8-4866-8fd8-17bd8a934597

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (key : Int) : VerinaSpec.Find_precond a key ↔ LLMSpec.precondition a key

- theorem postcondition_equiv (a : Array Int) (key : Int) (result : Int) : LLMSpec.precondition a key →
  (VerinaSpec.Find_postcond a key result ↔ LLMSpec.postcondition a key result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def Find_precond (a : Array Int) (key : Int) : Prop :=
  True

def Find_postcond (a : Array Int) (key : Int) (result: Int) :=
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)

end VerinaSpec

namespace LLMSpec

-- Helper: key is absent from the array
def keyAbsent (a : Array Int) (key : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≠ key

-- Helper: key is present in the array
def keyPresent (a : Array Int) (key : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = key

-- No preconditions
def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  (result = (-1) ∧ keyAbsent a key) ∨
  (result ≠ (-1) ∧
    0 ≤ result ∧
    (Int.toNat result) < a.size ∧
    a[(Int.toNat result)]! = key ∧
    (∀ (j : Nat), j < (Int.toNat result) → a[j]! ≠ key))

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (key : Int) : VerinaSpec.Find_precond a key ↔ LLMSpec.precondition a key := by
  -- Since both preconditions are defined as True, their equivalence is trivial.
  simp [VerinaSpec.Find_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Int) : LLMSpec.precondition a key →
  (VerinaSpec.Find_postcond a key result ↔ LLMSpec.postcondition a key result) := by
  -- By definition of `Find_postcond` and `postcondition`, we can split into cases based on whether `result` is -1 or not.
  by_cases h : result = -1 <;> simp [h, VerinaSpec.Find_postcond, LLMSpec.postcondition];
  · -- By definition of `LLMSpec.keyAbsent`, we have that `LLMSpec.keyAbsent a key` is equivalent to `∀ i < a.size, ¬a[i]! = key`.
    simp [LLMSpec.keyAbsent];
  · grind +ring

end Proof