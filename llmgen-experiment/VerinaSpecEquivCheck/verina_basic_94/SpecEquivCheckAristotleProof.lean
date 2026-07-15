/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 11c592e3-972e-489f-ab9e-ab5cc4d814cd

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int) : VerinaSpec.iter_copy_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : Array Int) (result : Array Int) : LLMSpec.precondition s →
  (VerinaSpec.iter_copy_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def iter_copy_precond (s : Array Int) : Prop :=
  True

def iter_copy_postcond (s : Array Int) (result: Array Int) :=
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)

end VerinaSpec

namespace LLMSpec

def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  (∀ (i : Nat), i < s.size → result[i]! = s[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (s : Array Int) : VerinaSpec.iter_copy_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.iter_copy_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : Array Int) (result : Array Int) : LLMSpec.precondition s →
  (VerinaSpec.iter_copy_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- By definition of `VerinaSpec.iter_copy_postcond`, we know that if `VerinaSpec.iter_copy_postcond s result` holds, then `result` is a copy of `s`.
  intro h_pre
  simp [VerinaSpec.iter_copy_postcond, LLMSpec.postcondition];
  -- The two conditions are equivalent because equality is symmetric.
  simp [eq_comm]

end Proof