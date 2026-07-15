/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0fae858f-2230-48dc-996e-ef0e708bfdcc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Int) : VerinaSpec.isEven_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isEven_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isEven_precond (n : Int) : Prop :=
  True

def isEven_postcond (n : Int) (result: Bool) :=
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

end VerinaSpec

namespace LLMSpec

-- No helper functions are required: Mathlib provides the predicate `Even n : Prop` for integers.

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ Even n) ∧
  (result = false ↔ ¬ Even n)

end LLMSpec

section Proof

theorem precondition_equiv (n : Int) : VerinaSpec.isEven_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.isEven_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Int) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isEven_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- The postcondition for VerinaSpec is equivalent to LLMSpec'spostcondition because `n % 2 = 0` is equivalent to `Even n`.
  simp [VerinaSpec.isEven_postcond, LLMSpec.postcondition, Int.even_iff];
  -- By definition of even and odd, we can split the conjunction into two implications.
  by_cases h : result = Bool.true <;> simp [h]

end Proof