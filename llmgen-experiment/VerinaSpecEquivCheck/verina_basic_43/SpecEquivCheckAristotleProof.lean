/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0b030a7d-117d-4bef-89d2-d831d349776d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  True

def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) :=
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)

end VerinaSpec

namespace LLMSpec

-- We use a closed-form characterization that uniquely determines the sum.
-- We avoid division in the postcondition by expressing the identity after multiplying by 15.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result * 15 = n * (2 * n - 1) * (2 * n + 1) * (12 * n * n - 7)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.sumOfFourthPowerOfOddNumbers_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.sumOfFourthPowerOfOddNumbers_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Nat) : LLMSpec.precondition n →
  (VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond n result ↔ LLMSpec.postcondition n result) := by
  unfold LLMSpec.precondition VerinaSpec.sumOfFourthPowerOfOddNumbers_postcond LLMSpec.postcondition; norm_num;
  rw [ mul_comm ] ; rcases n with ( _ | _ | n ) <;> norm_num at *;
  zify [ Nat.succ_mul ] ; ring;
  repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat nlinarith;
  · ring;
  · exact le_tsub_of_add_le_left ( by nlinarith )

end Proof