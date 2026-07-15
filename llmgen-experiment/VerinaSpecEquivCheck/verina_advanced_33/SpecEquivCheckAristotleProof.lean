/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 89746a68-1053-42ca-a637-e2fe3656d755

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.longestIncreasingSubsequence_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingSubsequence_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic

import Mathlib.Data.List.Basic


namespace VerinaSpec

def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing if it is pairwise related by `<`.
-- This implies each element is < every later element, and in particular adjacent elements increase.
-- It also holds for [] and singletons.
def StrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (fun (a : Int) (b : Int) => a < b)

-- `List.Sublist sub nums` is the standard Mathlib relation for an order-preserving subsequence.
def IsIncSubseq (sub : List Int) (nums : List Int) : Prop :=
  List.Sublist sub nums ∧ StrictlyIncreasing sub

-- No input restrictions.
def precondition (nums : List Int) : Prop :=
  True

-- The result is the length of a longest strictly increasing subsequence:
-- (1) there exists an increasing subsequence with length exactly `result`
-- (2) every increasing subsequence has length at most `result`
def postcondition (nums : List Int) (result : Nat) : Prop :=
  (∃ sub : List Int, IsIncSubseq sub nums ∧ sub.length = result) ∧
  (∀ sub : List Int, IsIncSubseq sub nums → sub.length ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.longestIncreasingSubsequence_precond nums ↔ LLMSpec.precondition nums := by
  -- Since both preconditions are True, they are equivalent.
  simp [VerinaSpec.longestIncreasingSubsequence_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingSubsequence_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  -- Since the preconditions are equivalent, we can focus on the postconditions.
  simp [VerinaSpec.longestIncreasingSubsequence_postcond, LLMSpec.postcondition];
  -- By definition of `IsIncSubseq`, we know that `sub` is a sublist of `nums` and is strictly increasing.
  simp [LLMSpec.IsIncSubseq] at *;
  -- By definition of `foldl`, the list of subsequences generated is exactly the list of all possible subsequences of `nums`.
  have h_foldl : ∀ (L : List ℤ), List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] L = List.map (fun sub => sub.reverse) (List.sublists L) := by
    intro L; induction' L using List.reverseRecOn with L ih <;> simp_all +decide [ List.sublists_cons ] ;
  simp_all +decide [ LLMSpec.StrictlyIncreasing ];
  grind

end Proof