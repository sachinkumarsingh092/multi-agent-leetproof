/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: af3f9b65-0266-4b32-9ecc-54d4cfc19eb5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : List Nat) : VerinaSpec.smallestMissingNumber_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : List Nat) (result : Nat) : LLMSpec.precondition s →
  (VerinaSpec.smallestMissingNumber_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def smallestMissingNumber_precond (s : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) s

def smallestMissingNumber_postcond (s : List Nat) (result: Nat) :=
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)

end VerinaSpec

namespace LLMSpec

-- A value is “missing” from the list if it is not a member.
-- “Smallest missing” is characterized by non-membership plus membership of all smaller naturals.

def precondition (s : List Nat) : Prop :=
  s.Sorted (· ≤ ·)

def postcondition (s : List Nat) (result : Nat) : Prop :=
  (result ∉ s) ∧
  (∀ (n : Nat), n < result → n ∈ s)

end LLMSpec

section Proof

theorem precondition_equiv (s : List Nat) : VerinaSpec.smallestMissingNumber_precond s ↔ LLMSpec.precondition s := by
  -- The two preconditions are equivalent because they both state that the list is pairwise sorted.
  simp [VerinaSpec.smallestMissingNumber_precond, LLMSpec.precondition];
  -- The definitions of pairwise and sorted are equivalent for the ≤ relation.
  simp [List.Pairwise, List.Sorted]

theorem postcondition_equiv (s : List Nat) (result : Nat) : LLMSpec.precondition s →
  (VerinaSpec.smallestMissingNumber_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- By definition of `smallestMissingNumber_postcond` and `postcondition`, we can see that they are equivalent if `s` is sorted.
  intro hs_sorted
  simp [VerinaSpec.smallestMissingNumber_postcond, LLMSpec.postcondition]

end Proof