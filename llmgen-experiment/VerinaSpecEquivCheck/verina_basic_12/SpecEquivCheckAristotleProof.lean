/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7ee15728-d38a-48a3-bf25-d25cd11c2447

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (size : Nat) : VerinaSpec.cubeSurfaceArea_precond size ↔ LLMSpec.precondition size

- theorem postcondition_equiv (size : Nat) (result : Nat) : LLMSpec.precondition size →
  (VerinaSpec.cubeSurfaceArea_postcond size result ↔ LLMSpec.postcondition size result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def cubeSurfaceArea_precond (size : Nat) : Prop :=
  True

def cubeSurfaceArea_postcond (size : Nat) (result: Nat) :=
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0

end VerinaSpec

namespace LLMSpec

-- No preconditions are needed because the input is a Nat (already nonnegative).
-- Kept as a separate definition to match the SpecDSL structure.
def precondition (size : Nat) : Prop :=
  True

-- The result is exactly the cube surface area using the standard formula.
def postcondition (size : Nat) (result : Nat) : Prop :=
  result = 6 * size * size

end LLMSpec

section Proof

theorem precondition_equiv (size : Nat) : VerinaSpec.cubeSurfaceArea_precond size ↔ LLMSpec.precondition size := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.cubeSurfaceArea_precond, LLMSpec.precondition]

theorem postcondition_equiv (size : Nat) (result : Nat) : LLMSpec.precondition size →
  (VerinaSpec.cubeSurfaceArea_postcond size result ↔ LLMSpec.postcondition size result) := by
  -- To prove the equivalence, we can show that the two conditions are equivalent by manipulating the equations.
  intros h_precond
  simp [VerinaSpec.cubeSurfaceArea_postcond, LLMSpec.postcondition];
  grind +ring

end Proof