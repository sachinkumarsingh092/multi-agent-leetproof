/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 394fb843-3fa9-4700-a051-9c97eb3c1a65

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.lastDigit_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.lastDigit_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def lastDigit_precond (n : Nat) : Prop :=
  True

def lastDigit_postcond (n : Nat) (result: Nat) :=
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)

end VerinaSpec

namespace LLMSpec

-- Helper definition: being a decimal digit (0..9) for natural numbers.
def IsDecimalDigit (d : Nat) : Prop := d < 10

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = n % 10 ∧ IsDecimalDigit result

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.lastDigit_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.lastDigit_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.lastDigit_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- By definition of `lastDigit_postcond` and `postcondition`, we can see that they are equivalent.
  simp [VerinaSpec.lastDigit_postcond, LLMSpec.postcondition];
  -- By definition of `IsDecimalDigit`, we know that `result < 10` if and only if `result` is a decimal digit.
  simp [LLMSpec.IsDecimalDigit];
  grind

end Proof