/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7924b823-be92-4f3d-8875-bdb1b4edb186

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (X : Int) (Y : Int) : VerinaSpec.SwapArithmetic_precond X Y ↔ LLMSpec.precondition X Y

- theorem postcondition_equiv (X : Int) (Y : Int) (result : (Int × Int)) : LLMSpec.precondition X Y →
  (VerinaSpec.SwapArithmetic_postcond X Y result ↔ LLMSpec.postcondition X Y result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  True

def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) :=
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

end VerinaSpec

namespace LLMSpec

-- No helper functions are required: the specification is fully described
-- by properties of the pair projections `fst` and `snd`.

def precondition (X : Int) (Y : Int) : Prop :=
  True

def postcondition (X : Int) (Y : Int) (result : (Int × Int)) : Prop :=
  result.fst = Y ∧ result.snd = X

end LLMSpec

section Proof

theorem precondition_equiv (X : Int) (Y : Int) : VerinaSpec.SwapArithmetic_precond X Y ↔ LLMSpec.precondition X Y := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.SwapArithmetic_precond, LLMSpec.precondition]

theorem postcondition_equiv (X : Int) (Y : Int) (result : (Int × Int)) : LLMSpec.precondition X Y →
  (VerinaSpec.SwapArithmetic_postcond X Y result ↔ LLMSpec.postcondition X Y result) := by
  -- Since the preconditions are the same and the postconditions are the same, the equivalence holds.
  simp [VerinaSpec.SwapArithmetic_postcond, LLMSpec.postcondition];
  -- Since the preconditions are the same and the postconditions are the same, the equivalence holds. We can use the fact that if X ≠ Y, then Y ≠ X.
  intros h_pre h_fst h_snd h_ne
  aesop

end Proof