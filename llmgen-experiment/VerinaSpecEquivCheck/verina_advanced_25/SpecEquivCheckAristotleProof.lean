/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e79e81ee-f825-475b-88f7-f8ac86862e3c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.lengthOfLIS_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.lengthOfLIS_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic

import Mathlib.Data.List.Basic


namespace VerinaSpec

def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0

def lengthOfLIS_postcond (nums : List Int) (result: Nat) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing when it is pairwise ordered by <.
-- This is Mathlib's `List.Pairwise` specialized to `<` on `Int`.
def StrictlyIncreasing (s : List Int) : Prop :=
  s.Pairwise (fun a b => a < b)

-- `s` is a strictly increasing subsequence of `nums`.
-- We use Mathlib's `List.Sublist` (a.k.a. `Sublist`, order-preserving deletion).
def IsStrictIncSubseq (s : List Int) (nums : List Int) : Prop :=
  List.Sublist s nums ∧ StrictlyIncreasing s

-- No preconditions: any integer list is allowed.
def precondition (nums : List Int) : Prop :=
  True

-- `result` is the maximum length of any strictly increasing subsequence.
-- We specify this via:
-- 1) Achievability: there exists a strictly increasing subsequence of length `result`.
-- 2) Maximality: every strictly increasing subsequence has length ≤ `result`.
def postcondition (nums : List Int) (result : Nat) : Prop :=
  (∃ s : List Int, IsStrictIncSubseq s nums ∧ s.length = result) ∧
  (∀ s : List Int, IsStrictIncSubseq s nums → s.length ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.lengthOfLIS_precond nums ↔ LLMSpec.precondition nums := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.lengthOfLIS_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.lengthOfLIS_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold LLMSpec.postcondition VerinaSpec.lengthOfLIS_postcond;
  -- By definition of `IsStrictIncSubseq`, we know that `s` is a strictly increasing subsequence of `nums` if and only if `s` is a sublist of `nums` and `s` is strictly increasing.
  have h_subseq : ∀ s : List ℤ, s ∈ List.map List.reverse (List.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] nums) ↔ s.Sublist nums := by
    induction nums using List.reverseRecOn <;> simp_all +decide [ List.sublist_append_right ];
    intro s; constructor <;> intro hs <;> simp_all +decide [ List.sublist_append_iff ] ;
    · grind +ring;
    · grind +ring;
  -- By definition of `IsStrictIncSubseq`, we know that `s` is a strictly increasing subsequence of `nums` if and only if `s` is a sublist of `nums` and `s` is strictly increasing. Therefore, the two postconditions are equivalent.
  simp [h_subseq, LLMSpec.IsStrictIncSubseq];
  simp +decide [ LLMSpec.StrictlyIncreasing ];
  grind +ring

end Proof