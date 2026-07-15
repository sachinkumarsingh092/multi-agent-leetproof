/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e49dc601-4ba4-4058-8797-2936b8588c3c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int) : VerinaSpec.isDivisibleBy11_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isDivisibleBy11_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def isDivisibleBy11_precond (n : Int) : Prop :=
  True

def isDivisibleBy11_postcond (n : Int) (result: Bool) :=
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))

end VerinaSpec

namespace LLMSpec

-- No helper functions are required; Mathlib/Lean provides integer divisibility via (∣).

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ (11 : Int) ∣ n) ∧
  (result = false ↔ ¬ ((11 : Int) ∣ n))

end LLMSpec

section Proof

theorem precondition_equiv (n : Int) : VerinaSpec.isDivisibleBy11_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are defined as True, their equivalence is trivial.
  simp [VerinaSpec.isDivisibleBy11_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isDivisibleBy11_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- By definition of `isDivisibleBy11_postcond` and `postcondition`, we can split the implication into two parts.
  simp [VerinaSpec.isDivisibleBy11_postcond, LLMSpec.postcondition];
  cases result <;> simp_all +decide [ dvd_iff_exists_eq_mul_right ]

end Proof