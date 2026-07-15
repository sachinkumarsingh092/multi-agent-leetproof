/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d01dfcdd-0a2a-472f-bdb2-46028ca36388

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr1 : List Int) (arr2 : List Int) : VerinaSpec.mergeSortedLists_precond arr1 arr2 ↔ LLMSpec.precondition arr1 arr2

- theorem postcondition_equiv (arr1 : List Int) (arr2 : List Int) (result : List Int) : LLMSpec.precondition arr1 arr2 →
  (VerinaSpec.mergeSortedLists_postcond arr1 arr2 result ↔ LLMSpec.postcondition arr1 arr2 result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2

def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result

end VerinaSpec

namespace LLMSpec

-- A simple, count-based multiset equality notion for lists of Int.
-- This avoids needing a separate reference implementation while precisely capturing
-- that the result contains exactly the elements from both inputs, with multiplicity.
def sameBag (a : List Int) (b : List Int) : Prop :=
  ∀ x : Int, a.count x = b.count x

-- Preconditions: both inputs are sorted ascending.
-- We use Mathlib's `List.Sorted` predicate.
def precondition (arr1 : List Int) (arr2 : List Int) : Prop :=
  arr1.Sorted (· ≤ ·) ∧ arr2.Sorted (· ≤ ·)

-- Postconditions:
-- 1) result is sorted ascending
-- 2) result has exactly the same multiset of elements as arr1 ++ arr2
-- 3) result length is the sum of the input lengths
-- Together these characterize the intended merge result.
def postcondition (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧
  sameBag result (arr1 ++ arr2) ∧
  result.length = arr1.length + arr2.length

end LLMSpec

section Proof

theorem precondition_equiv (arr1 : List Int) (arr2 : List Int) : VerinaSpec.mergeSortedLists_precond arr1 arr2 ↔ LLMSpec.precondition arr1 arr2 := by
  -- The preconditions are equivalent because `List.Pairwise (· ≤ ·)` is equivalent to `List.Sorted (· ≤ ·)`.
  simp [VerinaSpec.mergeSortedLists_precond, LLMSpec.precondition, List.Sorted]

theorem postcondition_equiv (arr1 : List Int) (arr2 : List Int) (result : List Int) : LLMSpec.precondition arr1 arr2 →
  (VerinaSpec.mergeSortedLists_postcond arr1 arr2 result ↔ LLMSpec.postcondition arr1 arr2 result) := by
  -- If the lists are sorted, then any permutation of their concatenation is also sorted.
  intro h_sorted
  apply Iff.intro;
  · -- If the result is sorted and a permutation of the concatenation, then it satisfies the postcondition.
    intro h_postcond
    obtain ⟨h_sorted, h_perm⟩ := h_postcond;
    refine' ⟨ h_sorted, _, _ ⟩ <;> simp_all +decide [ List.isPerm_iff ];
    · exact fun x => by rw [ h_perm.count_eq ] ;
    · simpa using h_perm.length_eq.symm;
  · -- If the postcondition holds, then the result is sorted and a permutation of arr1 ++ arr2.
    intro h_post
    obtain ⟨h_sorted, h_perm, h_len⟩ := h_post;
    refine' ⟨ h_sorted, _ ⟩;
    -- Since the counts of all elements in result and arr1 ++ arr2 are the same, they are permutations of each other.
    have h_perm_eq : List.Perm result (arr1 ++ arr2) := by
      exact?;
    exact?

end Proof