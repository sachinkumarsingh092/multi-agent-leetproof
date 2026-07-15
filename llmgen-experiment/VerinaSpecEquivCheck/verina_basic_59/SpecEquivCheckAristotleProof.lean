/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8548de82-6e44-409e-b38b-685906419a94

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int) : VerinaSpec.DoubleQuadruple_precond x ↔ LLMSpec.precondition x

- theorem postcondition_equiv (x : Int) (result : (Int × Int)) : LLMSpec.precondition x →
  (VerinaSpec.DoubleQuadruple_postcond x result ↔ LLMSpec.postcondition x result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def DoubleQuadruple_precond (x : Int) : Prop :=
  True

def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) :=
  result.fst = 2 * x ∧ result.snd = 2 * result.fst

end VerinaSpec

namespace LLMSpec

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : (Int × Int)) : Prop :=
  result.1 = (2 : Int) * x ∧
  result.2 = (4 : Int) * x

end LLMSpec

section Proof

theorem precondition_equiv (x : Int) : VerinaSpec.DoubleQuadruple_precond x ↔ LLMSpec.precondition x := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.DoubleQuadruple_precond, LLMSpec.precondition]

theorem postcondition_equiv (x : Int) (result : (Int × Int)) : LLMSpec.precondition x →
  (VerinaSpec.DoubleQuadruple_postcond x result ↔ LLMSpec.postcondition x result) := by
  -- By definition of postconditions, we can see that they are equivalent.
  simp [VerinaSpec.DoubleQuadruple_postcond, LLMSpec.postcondition];
  -- If result.1 is 2x, then 2 * result.1 is 4x. Therefore, the equivalence holds.
  intros h_pre h_eq
  rw [h_eq]
  ring

end Proof