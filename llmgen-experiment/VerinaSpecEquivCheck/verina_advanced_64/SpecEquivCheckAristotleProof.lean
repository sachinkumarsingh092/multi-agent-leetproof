/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a488779c-bf8c-4e8a-9f5d-ac50afe56941

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Nat) (target : Nat) : VerinaSpec.removeElement_precond lst target ↔ LLMSpec.precondition lst target

- theorem postcondition_equiv (lst : List Nat) (target : Nat) (result : List Nat) : LLMSpec.precondition lst target →
  (VerinaSpec.removeElement_postcond lst target result ↔ LLMSpec.postcondition lst target result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  True

def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat): Prop :=
  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length

end VerinaSpec

namespace LLMSpec

-- Helper-free specification:
-- We use `List.Sublist` to express order-preserving subsequence and `List.count`
-- to express multiplicity preservation.

def precondition (lst : List Nat) (target : Nat) : Prop :=
  True

def postcondition (lst : List Nat) (target : Nat) (result : List Nat) : Prop :=
  result.Sublist lst ∧
  result.count target = 0 ∧
  (∀ x : Nat, x ≠ target → result.count x = lst.count x)

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Nat) (target : Nat) : VerinaSpec.removeElement_precond lst target ↔ LLMSpec.precondition lst target := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.removeElement_precond, LLMSpec.precondition]

theorem postcondition_equiv (lst : List Nat) (target : Nat) (result : List Nat) : LLMSpec.precondition lst target →
  (VerinaSpec.removeElement_postcond lst target result ↔ LLMSpec.postcondition lst target result) := by
  intros h;
  -- To prove the equivalence, we can use the fact that if the elements are preserved and their counts are correct, then the order must also be preserved.
  apply Iff.intro;
  · -- If Verina's postcondition holds, then `result` is exactly the filtered list. Therefore, `result` is a sublist of `lst`, and the counts of elements match.
    intro h_verina
    have h_filter : result = lst.filter (fun x => x ≠ target) := by
      obtain ⟨h_zip, h_len⟩ := h_verina;
      refine' List.ext_get _ _ <;> simp_all +decide [ List.get?_eq_get ];
      intro n hn; specialize h_zip ( result[n] ) n; simp_all +decide [ List.getElem?_eq_getElem ] ;
      exact h_zip <| List.mem_iff_getElem.mpr ⟨ n, by aesop ⟩;
    -- Since `result` is equal to `lst.filter (fun x => x ≠ target)`, we can directly verify each part of the postcondition.
    simp [h_filter, LLMSpec.postcondition];
    -- Since the filtered list contains no elements equal to the target, the count of the target in the filtered list is zero.
    simp [List.count_eq_zero_of_not_mem];
    intro x hx; rw [ List.count_filter ] ; aesop;
  · -- If the result is a sublist of the original list and the counts are preserved, then the elements in the result must be in the same order as they were in the original list, just without the target.
    intro h_post
    have h_order : result.Sublist (lst.filter (fun x => x ≠ target)) := by
      -- Since the result is a sublist of the original list and has no target elements, it must be a sublist of the filtered list where the target elements are removed.
      have h_sublist : result.Sublist lst ∧ ∀ x ∈ result, x ≠ target := by
        -- By definition of `postcondition`, we know that `result.Sublist lst` and `result.count target = 0`.
        obtain ⟨h_sublist, h_count⟩ := h_post;
        exact ⟨ h_sublist, fun x hx => by rintro rfl; exact absurd h_count.1 ( by rw [ List.count_eq_zero ] ; aesop ) ⟩;
      have h_sublist_filter : ∀ {l1 l2 : List ℕ}, l1.Sublist l2 → (∀ x ∈ l1, x ≠ target) → l1.Sublist (List.filter (fun x => x ≠ target) l2) := by
        intros l1 l2 h_sublist h_no_target; induction' h_sublist with x l1 l2 h_sublist ih; aesop;
        · by_cases h : l2 = target <;> aesop;
        · grind;
      exact h_sublist_filter h_sublist.1 h_sublist.2;
    have h_length : result.length = (lst.filter (fun x => x ≠ target)).length := by
      have h_count : List.count target result = 0 ∧ ∀ x, x ≠ target → List.count x result = List.count x lst := by
        exact ⟨ h_post.2.1, h_post.2.2 ⟩;
      have h_count_eq : ∀ x, List.count x result = List.count x (lst.filter (fun x => x ≠ target)) := by
        intro x; by_cases hx : x = target <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
      have h_count_eq : Multiset.ofList result = Multiset.ofList (lst.filter (fun x => x ≠ target)) := by
        ext x; specialize h_count_eq x; aesop;
      simpa using congr_arg Multiset.card h_count_eq;
    -- Since the elements of the result are in the same order as the original list and their counts are preserved, the zipIdx condition holds.
    have h_zipIdx : ∀ i < result.length, result.get! i = (lst.filter (fun x => x ≠ target)).get! i := by
      have := List.Sublist.eq_of_length_le h_order; aesop;
    refine' ⟨ _, _ ⟩;
    · grind;
    · exact h_length

end Proof