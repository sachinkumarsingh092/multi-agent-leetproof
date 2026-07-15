/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8a8b4fb5-f4c7-42e9-8a28-9a809883a50f

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
  lst.length > 0

def maxOfList_postcond (lst : List Nat) (result: Nat) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result

end VerinaSpec

namespace LLMSpec

-- A simple, property-based characterization of being a maximum element of a list.
-- We avoid defining a reference implementation; instead we specify membership and upper-bound.

def isMaxOfList (lst : List Nat) (m : Nat) : Prop :=
  m ∈ lst ∧ ∀ (x : Nat), x ∈ lst → x ≤ m

-- Precondition: the list is non-empty.
-- Using lst ≠ [] keeps the condition decidable and simple.
def precondition (lst : List Nat) : Prop :=
  lst ≠ []

-- Postcondition: result is a maximum element of the list.
def postcondition (lst : List Nat) (result : Nat) : Prop :=
  isMaxOfList lst result

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Nat) : VerinaSpec.maxOfList_precond lst ↔ LLMSpec.precondition lst := by
  -- The length of a list is greater than 0 if and only if the list is not empty.
  simp [VerinaSpec.maxOfList_precond, LLMSpec.precondition];
  -- The length of a list is positive if and only if the list is not empty.
  simp [List.length_pos_iff]

theorem postcondition_equiv (lst : List Nat) (result : Nat) : LLMSpec.precondition lst →
  (VerinaSpec.maxOfList_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  -- Given that the list is non-empty, we can use the fact that the postconditions of both specifications are equivalent.
  intro h_nonempty
  simp [VerinaSpec.maxOfList_postcond, LLMSpec.postcondition, LLMSpec.isMaxOfList]

end Proof