/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 40b47f88-ee29-40b6-87f2-8a0a31495900

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (numbers : List Int) : VerinaSpec.longestIncreasingSubsequence_precond numbers ↔ LLMSpec.precondition numbers

- theorem postcondition_equiv (numbers : List Int) (result : Nat) : LLMSpec.precondition numbers →
  (VerinaSpec.longestIncreasingSubsequence_postcond numbers result ↔ LLMSpec.postcondition numbers result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  True

def longestIncreasingSubsequence_postcond (numbers : List Int) (result: Nat) : Prop :=
  let allSubseq := (numbers.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing when all pairs of positions are strictly ordered.
-- `Pairwise (· < ·)` implies in particular that adjacent elements are strictly increasing.
def isStrictlyIncreasing (xs : List Int) : Prop :=
  xs.Pairwise (fun a b => a < b)

-- A subsequence relation: `xs` is a subsequence of `numbers` if it can be obtained
-- by deleting elements from `numbers` without reordering.
-- In this library setup, `List.Sublist` is the available relation for this notion.
def isSubsequence (xs : List Int) (numbers : List Int) : Prop :=
  List.Sublist xs numbers

def precondition (numbers : List Int) : Prop :=
  True

def postcondition (numbers : List Int) (result : Nat) : Prop :=
  (∃ (s : List Int),
      isSubsequence s numbers ∧
      isStrictlyIncreasing s ∧
      s.length = result) ∧
  (∀ (t : List Int),
      isSubsequence t numbers →
      isStrictlyIncreasing t →
      t.length ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (numbers : List Int) : VerinaSpec.longestIncreasingSubsequence_precond numbers ↔ LLMSpec.precondition numbers := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.longestIncreasingSubsequence_precond, LLMSpec.precondition]

theorem postcondition_equiv (numbers : List Int) (result : Nat) : LLMSpec.precondition numbers →
  (VerinaSpec.longestIncreasingSubsequence_postcond numbers result ↔ LLMSpec.postcondition numbers result) := by
  unfold LLMSpec.postcondition VerinaSpec.longestIncreasingSubsequence_postcond;
  -- By definition of `allSubseq`, it contains all subsequences of `numbers`.
  have h_allSubseq : List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] numbers = List.map (fun (s : List ℤ) => s.reverse) (List.sublists numbers) := by
    induction numbers using List.reverseRecOn <;> aesop;
  simp_all +decide [ LLMSpec.isSubsequence, LLMSpec.isStrictlyIncreasing ];
  grind +ring

end Proof