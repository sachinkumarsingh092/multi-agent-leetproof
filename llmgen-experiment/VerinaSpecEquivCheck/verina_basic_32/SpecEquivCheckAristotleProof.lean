/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 001d1626-c321-481b-960d-73cc58c99fd4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.swapFirstAndLast_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.swapFirstAndLast_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def swapFirstAndLast_precond (a : Array Int) : Prop :=
  a.size > 0

def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)

end VerinaSpec

namespace LLMSpec

-- Helper: the last valid index of a non-empty array
-- For a.size > 0, `a.size - 1` is the index of the last element.
def lastIdx (a : Array Int) : Nat :=
  a.size - 1

-- Precondition: array is non-empty
-- Using a decidable numeric comparison (good for SMT and computation).
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: result has same size, first/last swapped, middle unchanged.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (a.size = 1 → result[0]! = a[0]!) ∧
  (a.size ≥ 2 →
    result[0]! = a[lastIdx a]! ∧
    result[lastIdx a]! = a[0]! ∧
    (∀ (i : Nat), i < a.size → i ≠ 0 → i ≠ lastIdx a → result[i]! = a[i]!))

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.swapFirstAndLast_precond a ↔ LLMSpec.precondition a := by
  -- The preconditions are equivalent because they both state that the array's size is greater than 0.
  simp [VerinaSpec.swapFirstAndLast_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.swapFirstAndLast_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- By definition of `swapFirstAndLast_postcond` and `postcondition`, we can see that they are equivalent under the given conditions.
  intros ha
  simp [VerinaSpec.swapFirstAndLast_postcond, LLMSpec.postcondition, LLMSpec.lastIdx];
  rcases n : a.size with ( _ | _ | n ) <;> simp_all +decide;
  -- To prove the equivalence, we can split into cases based on the value of `i`.
  intros h_size h_first h_last
  apply Iff.intro;
  · intro h i hi hi0 hi1; rcases i with ( _ | i ) <;> simp_all +decide ;
    convert h i ( lt_of_le_of_ne ( by linarith ) hi1 ) using 1 <;> aesop;
  · grind +ring

end Proof