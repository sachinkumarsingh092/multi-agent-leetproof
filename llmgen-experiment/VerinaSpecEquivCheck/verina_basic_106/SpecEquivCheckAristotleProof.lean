/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 369efaa0-b087-4102-9732-b4425dca6d6f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.arraySum_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.arraySum_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

def arraySum_postcond (a : Array Int) (b : Array Int) (result: Array Int) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)

end VerinaSpec

namespace LLMSpec

-- Precondition: arrays must have equal size.
-- This matches the problem statement assumption and ensures index-wise correspondence.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

-- Postcondition: result has the same size and matches element-wise addition.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ (i : Nat), i < a.size → result[i]! = a[i]! + b[i]!

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.arraySum_precond a b ↔ LLMSpec.precondition a b := by
  -- The preconditions are equivalent by definition.
  simp [VerinaSpec.arraySum_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.arraySum_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- To prove the equivalence, we can show that the postconditions are equal under the assumption that the preconditions are equal by using the fact that equality is symmetric.
  intros h_pre
  apply Iff.intro (fun h => ⟨h.1, fun i hi => h.2 i hi ▸ rfl⟩) (fun h => ⟨h.1, fun i hi => h.2 i hi ▸ rfl⟩)

end Proof