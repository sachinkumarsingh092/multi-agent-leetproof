/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 06e5493c-fcd0-4f1f-b5a6-f28e3822ad67

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int) : VerinaSpec.ComputeAvg_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Int) (b : Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.ComputeAvg_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  True

def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) :=
  2 * result = a + b - ((a + b) % 2)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: result is the floor of s/2, expressed without using division.
-- This uniquely determines result for all integers s.
def isFloorHalf (s : Int) (result : Int) : Prop :=
  (2 * result ≤ s) ∧ (s < 2 * (result + 1))

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  let s : Int := a + b
  isFloorHalf s result ∧
  (s - 1 ≤ 2 * result) ∧ (2 * result ≤ s + 1)

end LLMSpec

section Proof

theorem precondition_equiv (a : Int) (b : Int) : VerinaSpec.ComputeAvg_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.ComputeAvg_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.ComputeAvg_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- To prove the equivalence, we can show that the two conditions are equivalent by manipulating the inequalities and equalities.
  simp [VerinaSpec.ComputeAvg_postcond, LLMSpec.postcondition, LLMSpec.isFloorHalf];
  grind

end Proof