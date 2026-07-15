/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b3e8b3c5-99a3-477a-9e6c-b507cfaa668b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (l : List Nat) : VerinaSpec.smallestMissing_precond l ↔ LLMSpec.precondition l

- theorem postcondition_equiv (l : List Nat) (result : Nat) : LLMSpec.precondition l →
  (VerinaSpec.smallestMissing_postcond l result ↔ LLMSpec.postcondition l result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def smallestMissing_precond (l : List Nat) : Prop :=
  List.Pairwise (· < ·) l

def smallestMissing_postcond (l : List Nat) (result: Nat) : Prop :=
  result ∉ l ∧ ∀ candidate : Nat, candidate < result → candidate ∈ l

end VerinaSpec

namespace LLMSpec

-- `result` is the minimal excluded natural number (mex) of `l`.
-- This property uniquely characterizes the intended output.
def isMex (l : List Nat) (result : Nat) : Prop :=
  result ∉ l ∧ (∀ (n : Nat), n < result → n ∈ l)

-- The task statement says the input list is sorted in increasing order.
def precondition (l : List Nat) : Prop :=
  l.Sorted (· < ·)

def postcondition (l : List Nat) (result : Nat) : Prop :=
  isMex l result

end LLMSpec

section Proof

theorem precondition_equiv (l : List Nat) : VerinaSpec.smallestMissing_precond l ↔ LLMSpec.precondition l := by
  -- Since the list is in increasing order, it is already sorted.
  simp [VerinaSpec.smallestMissing_precond, LLMSpec.precondition];
  -- The equivalence follows directly from the definition of `List.Sorted`.
  simp [List.Sorted]

theorem postcondition_equiv (l : List Nat) (result : Nat) : LLMSpec.precondition l →
  (VerinaSpec.smallestMissing_postcond l result ↔ LLMSpec.postcondition l result) := by
  -- If the list is sorted in increasing order, then the smallest missing number is the same as the mex.
  intro h_sorted
  simp [VerinaSpec.smallestMissing_postcond, LLMSpec.postcondition];
  -- By definition of `isMex`, we know that `isMex l result` is equivalent to `result ∉ l ∧ ∀ candidate < result, candidate ∈ l`.
  simp [LLMSpec.isMex]

end Proof