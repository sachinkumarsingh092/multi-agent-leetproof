/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5be1ae3e-dbce-4616-b8ae-93bb85b0006d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) (k : Nat) : VerinaSpec.kthElement_precond arr k ↔ LLMSpec.precondition arr k

- theorem postcondition_equiv (arr : Array Int) (k : Nat) (result : Int) : LLMSpec.precondition arr k →
  (VerinaSpec.kthElement_postcond arr k result ↔ LLMSpec.postcondition arr k result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  k ≥ 1 ∧ k ≤ arr.size

def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) :=
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)

end VerinaSpec

namespace LLMSpec

-- Helper: the corresponding 0-based index for a 1-based position.
-- Note: this is only meaningful when k ≥ 1.
def idx0 (k : Nat) : Nat := k - 1

def precondition (arr : Array Int) (k : Nat) : Prop :=
  arr.size > 0 ∧ 1 ≤ k ∧ k ≤ arr.size

def postcondition (arr : Array Int) (k : Nat) (result : Int) : Prop :=
  -- Because k is within [1, arr.size], (k-1) is a valid 0-based index.
  result = arr[idx0 k]!

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (k : Nat) : VerinaSpec.kthElement_precond arr k ↔ LLMSpec.precondition arr k := by
  -- The two preconditions are equivalent because they both require the array to be non-empty and k to be within the valid range.
  simp [VerinaSpec.kthElement_precond, LLMSpec.precondition];
  grind

theorem postcondition_equiv (arr : Array Int) (k : Nat) (result : Int) : LLMSpec.precondition arr k →
  (VerinaSpec.kthElement_postcond arr k result ↔ LLMSpec.postcondition arr k result) := by
  -- By definition of `precondition`, we know that `k` is within the bounds of `arr`.
  intro h_precondition
  simp [VerinaSpec.kthElement_postcond, LLMSpec.postcondition];
  -- If there exists an index i such that arr[i] = result and arr[i] = arr[k-1]!, then result must be equal to arr[k-1]!.
  apply Iff.intro
  intro h
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := h
  aesop;
  -- Since $k$ is within the bounds of the array, $k-1$ is a valid index.
  have h_valid_index : k - 1 < arr.size := by
    exact Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt h_precondition.2.1 ) ) h_precondition.2.2;
  -- Since $k-1$ is a valid index, we can use it directly.
  use fun h => ⟨k - 1, h_valid_index, by
    convert h.symm;
    exact Eq.symm ( by exact dif_pos h_valid_index ), by
    exact?⟩

end Proof