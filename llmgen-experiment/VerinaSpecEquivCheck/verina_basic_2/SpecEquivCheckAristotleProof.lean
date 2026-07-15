/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e0ec1cc5-0592-4141-9997-124aba26d554

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Nat) : VerinaSpec.findSmallest_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : Array Nat) (result : Option Nat) : LLMSpec.precondition s →
  (VerinaSpec.findSmallest_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def findSmallest_precond (s : Array Nat) : Prop :=
  True

def findSmallest_postcond (s : Array Nat) (result: Option Nat) :=
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)

end VerinaSpec

namespace LLMSpec

def precondition (s : Array Nat) : Prop :=
  True

def postcondition (s : Array Nat) (result : Option Nat) : Prop :=
  match result with
  | none => s.size = 0
  | some m =>
      s.size > 0 ∧ m ∈ s ∧ ∀ x : Nat, x ∈ s → m ≤ x

end LLMSpec

section Proof

theorem precondition_equiv (s : Array Nat) : VerinaSpec.findSmallest_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.findSmallest_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : Array Nat) (result : Option Nat) : LLMSpec.precondition s →
  (VerinaSpec.findSmallest_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- By definition of `findSmallest_postcond` and `postcondition`, we can split into cases based on the result.
  cases' result with r hr
  simp [VerinaSpec.findSmallest_postcond, LLMSpec.postcondition];
  -- By definition of `findSmallest_postcond` and `postcondition`, we can split into cases based on the result and the properties of the list.
  simp [VerinaSpec.findSmallest_postcond, LLMSpec.postcondition] at *;
  -- If there's an element in the array, then the array isn't empty, hence its size is positive.
  intro h_pre h_mem h_min
  apply Nat.pos_of_ne_zero
  intro h_zero
  aesop

end Proof