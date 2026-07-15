/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cb00e401-1f3e-4c1b-b8fa-658ad3a0caa6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Nat) : VerinaSpec.maxOfList_precond lst ↔ LLMSpec.precondition lst

- theorem postcondition_equiv (lst : List Nat) (result : Nat) : LLMSpec.precondition lst →
  (VerinaSpec.maxOfList_postcond lst result ↔ LLMSpec.postcondition lst result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def maxOfList_precond (lst : List Nat) : Prop :=
  lst ≠ []

-- Ensure the list is non-empty

def maxOfList_postcond (lst : List Nat) (result: Nat) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result

end VerinaSpec

namespace LLMSpec

-- A value is a maximum element of a list when it is contained in the list
-- and it is an upper bound for all elements of the list.

def precondition (lst : List Nat) : Prop :=
  lst ≠ []

def postcondition (lst : List Nat) (result : Nat) : Prop :=
  result ∈ lst ∧
  (∀ (x : Nat), x ∈ lst → x ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Nat) : VerinaSpec.maxOfList_precond lst ↔ LLMSpec.precondition lst := by
  -- The preconditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.maxOfList_precond, LLMSpec.precondition]

theorem postcondition_equiv (lst : List Nat) (result : Nat) : LLMSpec.precondition lst →
  (VerinaSpec.maxOfList_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  unfold LLMSpec.precondition VerinaSpec.maxOfList_postcond LLMSpec.postcondition; aesop;

end Proof