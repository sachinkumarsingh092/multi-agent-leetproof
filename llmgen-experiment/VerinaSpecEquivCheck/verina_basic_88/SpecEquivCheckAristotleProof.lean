/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 498a1d59-5838-44f7-b29b-5bf41b42becd

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) : VerinaSpec.ToArray_precond xs ↔ LLMSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Array Int) : LLMSpec.precondition xs →
  (VerinaSpec.ToArray_postcond xs result ↔ LLMSpec.postcondition xs result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def ToArray_precond (xs : List Int) : Prop :=
  True

def ToArray_postcond (xs : List Int) (result: Array Int) :=
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!

end VerinaSpec

namespace LLMSpec

-- No helper functions are required.

def precondition (xs : List Int) : Prop :=
  True

def postcondition (xs : List Int) (result : Array Int) : Prop :=
  result.size = xs.length ∧
  ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) : VerinaSpec.ToArray_precond xs ↔ LLMSpec.precondition xs := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.ToArray_precond, LLMSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : Array Int) : LLMSpec.precondition xs →
  (VerinaSpec.ToArray_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  -- By definition of `postcondition`, we need to show that `result.size = xs.length` and `∀ i < xs.length, result[i]! = xs[i]!`.
  simp [VerinaSpec.ToArray_postcond, LLMSpec.postcondition]

end Proof