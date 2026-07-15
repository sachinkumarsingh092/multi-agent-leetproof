/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5c0d17b1-d297-44ff-8885-b0a8c891ff91

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.containsConsecutiveNumbers_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.containsConsecutiveNumbers_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  True

def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) :=
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result

end VerinaSpec

namespace LLMSpec

-- Existence of an index with an adjacent consecutive step by +1.
def hasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ hasConsecutivePair a) ∧
  (result = false ↔ ¬ hasConsecutivePair a)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.containsConsecutiveNumbers_precond a ↔ LLMSpec.precondition a := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.containsConsecutiveNumbers_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.containsConsecutiveNumbers_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- Since the preconditions are the same, the postconditions must also be equivalent.
  simp [VerinaSpec.containsConsecutiveNumbers_postcond, LLMSpec.postcondition];
  -- Since the preconditions are the same, the postconditions must also be equivalent. We can use the fact that the existence of an index in `hasConsecutivePair` is equivalent to the existence of an index in the other definition.
  simp [LLMSpec.hasConsecutivePair];
  grind

end Proof