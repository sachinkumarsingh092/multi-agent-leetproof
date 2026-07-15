/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7a20abb0-5268-4ec4-a382-77b705b52fd1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) : VerinaSpec.insertionSort_precond xs ↔ LLMSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : List Int) : LLMSpec.precondition xs →
  (VerinaSpec.insertionSort_postcond xs result ↔ LLMSpec.postcondition xs result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def insertionSort_precond (xs : List Int) : Prop :=
  True

def insertionSort_postcond (xs : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

end VerinaSpec

namespace LLMSpec

def precondition (xs : List Int) : Prop :=
  True

def postcondition (xs : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ List.Perm xs result

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) : VerinaSpec.insertionSort_precond xs ↔ LLMSpec.precondition xs := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.insertionSort_precond, LLMSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : List Int) : LLMSpec.precondition xs →
  (VerinaSpec.insertionSort_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  -- By definition of `insertionSort_postcond` and `postcondition`, we can rewrite the goal in terms of the definitions.
  simp [VerinaSpec.insertionSort_postcond, LLMSpec.postcondition] at *;
  -- By definition of `List.Sorted` and `List.Perm`, we can rewrite the goal in terms of these definitions.
  simp [List.Sorted, List.Perm] at *;
  -- The equivalence follows directly from the definitions of `isPerm` and `Perm`.
  simp [List.isPerm_iff] at *

end Proof