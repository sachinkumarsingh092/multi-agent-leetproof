/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0074de16-04e0-40c0-8522-f0f91b6c1b29

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.ifPowerOfFour_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.ifPowerOfFour_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def ifPowerOfFour_precond (n : Nat) : Prop :=
  True

def ifPowerOfFour_postcond (n : Nat) (result: Bool) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: n is a power of four in the mathematical sense.
def IsPowerOfFour (n : Nat) : Prop :=
  ∃ (x : Nat), n = 4 ^ x

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsPowerOfFour n) ∧
  (result = false ↔ ¬ IsPowerOfFour n)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.ifPowerOfFour_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.ifPowerOfFour_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.ifPowerOfFour_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- Since the preconditions are equivalent, we can focus on the postconditions.
  simp [VerinaSpec.ifPowerOfFour_postcond, LLMSpec.postcondition];
  -- Since the postconditions are equivalent by definition, the proof is trivial.
  simp [LLMSpec.IsPowerOfFour];
  -- By definition of postcondition, we need to show that result is true if and only if n is a power of four.
  intro h_pre h_post
  cases result <;> simp_all +decide [ LLMSpec.IsPowerOfFour ]

end Proof