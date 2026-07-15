/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 28c49537-e884-48a9-a943-b3acd790e4fb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int) : VerinaSpec.hasOppositeSign_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Int) (b : Int) (result : Bool) : LLMSpec.precondition a b →
  (VerinaSpec.hasOppositeSign_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  True

def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) :=
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)

end VerinaSpec

namespace LLMSpec

-- We keep the specification purely relational over Int order comparisons.

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Bool) : Prop :=
  result = true ↔ ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0))

end LLMSpec

section Proof

theorem precondition_equiv (a : Int) (b : Int) : VerinaSpec.hasOppositeSign_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.hasOppositeSign_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (result : Bool) : LLMSpec.precondition a b →
  (VerinaSpec.hasOppositeSign_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- By definition of VerinaSpec.hasOppositeSign_postcond and LLMSpec.postcondition, we can show that they are equivalent by considering the cases where the conditions hold or not.
  simp [VerinaSpec.hasOppositeSign_postcond, LLMSpec.postcondition];
  -- By definition of VerinaSpec.hasOppositeSign_postcond and LLMSpec.postcondition, we can show that they are equivalent by considering the cases where the conditions hold or not. We'll use the fact that if the condition holds, then the result must be true, and if the condition doesn't hold, the result must be false.
  by_cases h : (a < 0 ∧ 0 < b ∨ 0 < a ∧ b < 0) <;> simp [h];
  · -- By definition of VerinaSpec.hasOppositeSign_postcond and LLMSpec.postcondition, we can show that they are equivalent by considering the cases where the conditions hold or not. We'll use the fact that if the condition holds, then the result must be true, and if the condition doesn't hold, the result must be false. We'll split into the two cases from h.
    cases h <;> simp_all +decide [ LLMSpec.precondition, VerinaSpec.hasOppositeSign_postcond ];
  · aesop

end Proof