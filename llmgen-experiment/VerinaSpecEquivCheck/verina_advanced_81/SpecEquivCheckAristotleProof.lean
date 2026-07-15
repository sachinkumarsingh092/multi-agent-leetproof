/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 34214703-4ee6-484d-8c1f-8f488a966adb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : List Int) : VerinaSpec.uniqueSorted_precond arr ↔ LLMSpec.precondition arr

- theorem postcondition_equiv (arr : List Int) (result : List Int) : LLMSpec.precondition arr →
  (VerinaSpec.uniqueSorted_postcond arr result ↔ LLMSpec.postcondition arr result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def uniqueSorted_precond (arr : List Int) : Prop :=
  True

def uniqueSorted_postcond (arr : List Int) (result: List Int) : Prop :=
  List.isPerm arr.eraseDups result ∧ List.Pairwise (· ≤ ·) result

end VerinaSpec

namespace LLMSpec

-- We use Mathlib's standard list predicates:
-- * `List.Nodup` for duplicate-freeness
-- * `List.Sorted (· ≤ ·)` for ascending order
-- * `x ∈ l` for membership

-- No preconditions are required.
def precondition (arr : List Int) : Prop :=
  True

def postcondition (arr : List Int) (result : List Int) : Prop :=
  result.Nodup ∧
  List.Sorted (· ≤ ·) result ∧
  (∀ x : Int, x ∈ result ↔ x ∈ arr)

end LLMSpec

section Proof

theorem precondition_equiv (arr : List Int) : VerinaSpec.uniqueSorted_precond arr ↔ LLMSpec.precondition arr := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.uniqueSorted_precond, LLMSpec.precondition]

theorem postcondition_equiv (arr : List Int) (result : List Int) : LLMSpec.precondition arr →
  (VerinaSpec.uniqueSorted_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  -- To prove the equivalence, we can show that the conditions are equivalent by using the fact that if the postconditions are equivalent, then the functions are equivalent.
  intro h_pre
  simp [VerinaSpec.uniqueSorted_postcond, LLMSpec.postcondition];
  constructor <;> intro h <;> simp_all +decide [ List.isPerm_iff ];
  · -- Since `arr.eraseDups` is a permutation of `result`, and `arr.eraseDups` has no duplicates, `result` must also have no duplicates.
    have h_nodup : result.Nodup := by
      have h_nodup : (arr.eraseDups).Nodup := by
        -- By definition of `eraseDups`, the resulting list has no duplicates.
        have h_eraseDups_nodup : ∀ (l : List ℤ), (l.eraseDups).Nodup := by
          intro l
          simp [List.eraseDups];
          -- By definition of `List.eraseDupsBy.loop`, the resulting list has no duplicates.
          have h_eraseDupsBy_loop_nodup : ∀ (l : List ℤ) (acc : List ℤ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
            intros l acc hacc_nodup
            induction' l with x l ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ];
            by_cases hx : x ∈ acc <;> simp_all +decide [ List.any_eq ];
          exact h_eraseDupsBy_loop_nodup _ _ ( by simp +decide );
        exact h_eraseDups_nodup arr;
      exact h.1.symm.nodup_iff.mpr h_nodup;
    have h_mem : ∀ x, x ∈ arr.eraseDups ↔ x ∈ arr := by
      -- By definition of `List.eraseDupsBy.loop`, the elements in the resulting list are exactly those elements of the original list that were not duplicates.
      have h_eraseDupsBy_loop : ∀ (l : List ℤ) (acc : List ℤ), (∀ x, x ∈ List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc ↔ x ∈ l ∨ x ∈ acc) := by
        intros l acc x; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
        by_cases h : acc.any ( fun x2 => hd == x2 ) <;> simp_all +decide [ List.any_eq ] ; aesop;
        grind;
      exact fun x => by simpa using h_eraseDupsBy_loop arr [ ] x;
    exact ⟨ h_nodup, h.2, fun x => by rw [ ← h.1.mem_iff, h_mem ] ⟩;
  · -- Since `result` is nodup and sorted, and `arr.eraseDups` is also nodup, they must be permutations of each other.
    have h_perm : List.Perm (arr.eraseDups) result := by
      have h_nodup : List.Nodup (arr.eraseDups) := by
        -- By definition of `List.eraseDupsBy.loop`, the list `arr.eraseDupsBy.loop (fun x1 x2 => x1 == x2) []` is nodup.
        have h_erase_dups_loop_nodup : ∀ (l : List ℤ) (acc : List ℤ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
          intros l acc hacc_nodup
          induction' l with x l ih generalizing acc;
          · simp [List.eraseDupsBy.loop];
            assumption;
          · unfold List.eraseDupsBy.loop; aesop;
        exact h_erase_dups_loop_nodup _ _ ( by simp +decide )
      have h_nodup_result : List.Nodup result := by
        exact h.1
      have h_eq : ∀ x, x ∈ arr.eraseDups ↔ x ∈ result := by
        have h_perm : ∀ l : List ℤ, ∀ x, x ∈ l.eraseDups ↔ x ∈ l := by
          intro l x; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.eraseDups_cons ] ;
          simp_all +decide [ List.eraseDups_append ];
          by_cases hx : x = ih <;> simp_all +decide [ List.removeAll ];
          · by_cases hi : ih ∈ l <;> simp_all +decide [ List.filter_cons ];
            simp +decide [ List.eraseDups_cons ];
          · grind +ring;
        aesop
      exact?;
    exact ⟨ h_perm, h.2.1 ⟩

end Proof