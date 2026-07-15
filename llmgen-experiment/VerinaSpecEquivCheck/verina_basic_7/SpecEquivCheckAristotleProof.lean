/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 36d31bce-b6f3-482f-8383-acb3bd5d16a1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.sumOfSquaresOfFirstNOddNumbers_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  True

def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) :=
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0

end VerinaSpec

namespace LLMSpec

-- Helper: the numerator polynomial appearing in the closed-form.
-- Note: Nat subtraction is truncated, but for n = 0 we still get numerator = 0.
def oddSquaresNumerator (n : Nat) : Nat :=
  n * (2 * n - 1) * (2 * n + 1)

-- No input restrictions: n is already non-negative by type.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is the unique Nat such that result*3 equals the numerator.
-- This avoids relying on truncating Nat division in the specification.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result * 3 = oddSquaresNumerator n

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.sumOfSquaresOfFirstNOddNumbers_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.sumOfSquaresOfFirstNOddNumbers_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- To prove the equivalence, we can show that the two conditions are equivalent by manipulating the equations.
  intro h_precond
  constructor
  intro h_postcond
  obtain ⟨h1, h2⟩ := h_postcond
  have h_eq : result = n * (2 * n - 1) * (2 * n + 1) / 3 := by
    omega
  have h_eq' : result * 3 = n * (2 * n - 1) * (2 * n + 1) := by
    rw [ h_eq, Nat.div_mul_cancel ];
    rw [ Nat.dvd_iff_mod_eq_zero ] ; rw [ ← Nat.mod_add_div n 3 ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ; have := Nat.mod_lt n zero_lt_three; interval_cases n % 3 <;> norm_num;
    grind +ring
  exact h_eq';
  -- If the postcondition holds, then the result is exactly the numerator divided by 3.
  intro h_postcond
  have h_eq : result = n * (2 * n - 1) * (2 * n + 1) / 3 := by
    -- By definition of postcondition, we have result * 3 = n * (2 * n - 1) * (2 * n + 1).
    have h_eq : result * 3 = n * (2 * n - 1) * (2 * n + 1) := by
      exact h_postcond;
    rw [ ← h_eq, Nat.mul_div_cancel _ ( by decide ) ];
  constructor <;> omega

end Proof