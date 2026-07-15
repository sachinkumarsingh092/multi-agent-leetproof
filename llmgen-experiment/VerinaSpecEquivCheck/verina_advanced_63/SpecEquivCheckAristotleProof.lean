/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aa7c0769-5d76-4a4d-865a-ccccdb5a2d66

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.removeDuplicates_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.removeDuplicates_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def removeDuplicates_precond (nums : List Int) : Prop :=
  List.Pairwise (· ≤ ·) nums

def removeDuplicates_postcond (nums : List Int) (result: Nat) : Prop :=
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result

end VerinaSpec

namespace LLMSpec

-- A list `u` represents the set of values appearing in `nums` when:
-- (a) `u` has no duplicates
-- (b) membership in `u` is equivalent to membership in `nums`
-- For a sorted input, such a `u` corresponds to the unique values.
def representsUniques (nums : List Int) (u : List Int) : Prop :=
  u.Nodup ∧ (∀ x : Int, x ∈ u ↔ x ∈ nums)

-- Precondition: the input list is sorted in non-decreasing order.
def precondition (nums : List Int) : Prop :=
  nums.Sorted (· ≤ ·)

-- Postcondition: the result equals the length of some duplicate-free list
-- that contains exactly the values appearing in `nums`.
-- This characterizes the number of distinct values in `nums`.
def postcondition (nums : List Int) (result : Nat) : Prop :=
  ∃ u : List Int,
    representsUniques nums u ∧
    result = u.length

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.removeDuplicates_precond nums ↔ LLMSpec.precondition nums := by
  -- The definitions of VerinaSpec.removeDuplicates_precond and LLMSpec.precondition are identical, so the equivalence is trivial.
  simp [VerinaSpec.removeDuplicates_precond, LLMSpec.precondition];
  -- The definitions of `List.Pairwise` and `List.Sorted` are equivalent for the given relation.
  simp [List.Pairwise, List.Sorted]

theorem postcondition_equiv (nums : List Int) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.removeDuplicates_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  intro h_sorted
  constructor;
  · -- Since `nums` is sorted, the list obtained by removing duplicates from `nums` is also sorted and has no duplicates.
    have h_unique : List.Nodup (nums.eraseDups) ∧ ∀ x, x ∈ nums.eraseDups ↔ x ∈ nums := by
      -- By definition of `List.eraseDupsBy.loop`, the resulting list is nodup and contains exactly the same elements as the original list.
      have h_erase_dups_loop : ∀ (l : List ℤ) (acc : List ℤ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) ∧ ∀ x, x ∈ List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc ↔ x ∈ l ∨ x ∈ acc := by
        intros l acc hacc_nodup
        induction' l with x l ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ];
        cases h : acc.any fun x2 => x == x2 <;> simp_all +decide [ List.any_eq ];
        · grind +ring;
        · grind +ring;
      simpa using h_erase_dups_loop nums [ ] ( by simp +decide );
    -- Use the fact that `nums.eraseDups` is a duplicate-free list that contains exactly the values appearing in `nums` to conclude the proof.
    use fun h => ⟨nums.eraseDups, h_unique, by
      exact Nat.sub_eq_zero_iff_le.mp h.1 |> le_antisymm <| h.2.trans' <| by aesop;⟩;
  · -- If there exists a list u that represents the uniques of nums, then the length of u is equal to the length of the list after removing duplicates.
    intro h_uniques
    obtain ⟨u, hu_unique, hu_length⟩ := h_uniques
    have h_erase_dups : u.length = (nums.eraseDups).length := by
      have h_erase_dups : u.toFinset = (nums.eraseDups).toFinset := by
        ext x; simp [hu_unique];
        -- Since $u$ represents the uniques in $nums$, $x \in u$ if and only if $x \in nums$.
        have h_uniques : x ∈ u ↔ x ∈ nums := by
          exact hu_unique.2 x;
        convert h_uniques using 1;
        -- By definition of `List.eraseDupsBy.loop`, the list `l` is a permutation of `nums` with duplicates removed.
        have h_perm : ∀ {l : List ℤ} {acc : List ℤ}, x ∈ List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc ↔ x ∈ l ∨ x ∈ acc := by
          intros l acc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
          by_cases h : hd ∈ acc <;> simp_all +decide [ List.any_eq ];
          · grind;
          · tauto;
        simpa using @h_perm nums [];
      rw [ ← List.toFinset_card_of_nodup hu_unique.1, h_erase_dups, List.toFinset_card_of_nodup ];
      -- By definition of `List.eraseDupsBy.loop`, the resulting list has no duplicates.
      have h_erase_dups_loop_nodup : ∀ (l : List ℤ) (acc : List ℤ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
        intros l acc hacc_nodup; induction' l with x l ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
        by_cases hx : x ∈ acc <;> simp_all +decide [ List.any_eq ];
      exact h_erase_dups_loop_nodup _ _ ( by simp +decide );
    unfold VerinaSpec.removeDuplicates_postcond; aesop;

end Proof