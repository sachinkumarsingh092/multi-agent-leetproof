/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 19acd147-6147-4b46-947f-b846f3c74f7b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (e : Int) : VerinaSpec.LinearSearch_precond a e ↔ LLMSpec.precondition a e

- theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) : LLMSpec.precondition a e →
  (VerinaSpec.LinearSearch_postcond a e result ↔ LLMSpec.postcondition a e result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  True

def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) :=
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)

end VerinaSpec

namespace LLMSpec

-- `result` is the first index where `a[result]! = e`, or `a.size` if `e` does not occur.

def precondition (a : Array Int) (e : Int) : Prop :=
  True

def postcondition (a : Array Int) (e : Int) (result : Nat) : Prop :=
  result ≤ a.size ∧
  ((result < a.size ∧ a[result]! = e ∧ (∀ j : Nat, j < result → a[j]! ≠ e)) ∨
   (result = a.size ∧ (∀ j : Nat, j < a.size → a[j]! ≠ e)))

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (e : Int) : VerinaSpec.LinearSearch_precond a e ↔ LLMSpec.precondition a e := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.LinearSearch_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) : LLMSpec.precondition a e →
  (VerinaSpec.LinearSearch_postcond a e result ↔ LLMSpec.postcondition a e result) := by
  -- By definition of `LinearSearch_postcond` and `postcondition`, they are equivalent when theprecondition holds. We can split into cases based on whether the result is less than the size of the array or equal to it.
  simp [VerinaSpec.LinearSearch_postcond, LLMSpec.postcondition];
  grind

end Proof