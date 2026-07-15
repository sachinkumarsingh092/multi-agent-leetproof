/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 768d0448-8586-491c-926e-c32fe0e44722

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.remove_front_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.remove_front_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def remove_front_precond (a : Array Int) : Prop :=
  a.size > 0

def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc

def remove_front_postcond (a : Array Int) (result: Array Int) :=
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)

end VerinaSpec

namespace LLMSpec

def precondition (a : Array Int) : Prop :=
  a.size > 0

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size - 1 ∧
  ∀ (i : Nat), i < result.size → result[i]! = a[i + 1]!

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.remove_front_precond a ↔ LLMSpec.precondition a := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.remove_front_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.remove_front_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- Since the preconditions are equivalent, we can use the fact that if the preconditions are equivalent, then the postconditions are equivalent under the same conditions.
  intro h_precond
  simp [VerinaSpec.remove_front_postcond, LLMSpec.postcondition];
  -- Since $a$ is non-empty, its size is positive.
  intro h_size h_cond
  exact h_precond

end Proof