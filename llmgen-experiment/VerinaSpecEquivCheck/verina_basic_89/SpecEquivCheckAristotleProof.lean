/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6d81838a-4df1-4797-bb03-cb8f34cc2848

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : List Int) : VerinaSpec.SetToSeq_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : List Int) (result : List Int) : LLMSpec.precondition s →
  (VerinaSpec.SetToSeq_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def SetToSeq_precond (s : List Int) : Prop :=
  True

def SetToSeq_postcond (s : List Int) (result: List Int) :=
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  result.all (fun a => result.count a = 1) ∧
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result

end VerinaSpec

namespace LLMSpec

-- x has its first occurrence in s exactly at position p.
-- This characterizes first occurrence without using any library index-finding API.
def FirstOccurrenceAt (x : Int) (s : List Int) (p : Nat) : Prop :=
  p < s.length ∧
  s[p]! = x ∧
  ∀ q : Nat, q < p → s[q]! ≠ x

def precondition (s : List Int) : Prop :=
  True

def postcondition (s : List Int) (result : List Int) : Prop :=
  -- No duplicates in the output.
  result.Nodup ∧
  -- Output contains exactly the elements that appear in the input.
  (∀ x : Int, x ∈ result ↔ x ∈ s) ∧
  -- Every output element is taken at its first occurrence position in s.
  (∀ i : Nat, i < result.length → ∃ p : Nat, FirstOccurrenceAt (result[i]!) s p) ∧
  -- The first-occurrence positions of elements of result are strictly increasing in result order.
  (∀ i j : Nat, i < j → j < result.length →
    ∃ pi pj : Nat,
      FirstOccurrenceAt (result[i]!) s pi ∧
      FirstOccurrenceAt (result[j]!) s pj ∧
      pi < pj)

end LLMSpec

section Proof

theorem precondition_equiv (s : List Int) : VerinaSpec.SetToSeq_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.SetToSeq_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : List Int) (result : List Int) : LLMSpec.precondition s →
  (VerinaSpec.SetToSeq_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- To prove the equivalence, we can show that the conditions in VerinaSpec.SetToSeq_postcond imply the conditions in LLMSpec.postcondition and vice versa.
  intros h_precond
  constructor;
  · unfold VerinaSpec.SetToSeq_postcond LLMSpec.postcondition;
    -- By definition of VerinaSpec.SetToSeq_postcond, we know that result is a permutation of s with no duplicates.
    intro h
    have h_nodup : result.Nodup := by
      rw [ List.nodup_iff_count_eq_one ] ; aesop
    have h_elements : ∀ x, x ∈ result ↔ x ∈ s := by
      grind
    have h_first_occurrence : ∀ i < result.length, ∃ p, LLMSpec.FirstOccurrenceAt result[i]! s p := by
      intro i hi
      use s.idxOf (result[i]!);
      -- Since $x$ is in $s$, the index of $x$ in $s$ is the first occurrence of $x$ in $s$.
      have h_first_occurrence : ∀ x ∈ s, List.idxOf x s < s.length ∧ s[List.idxOf x s]! = x ∧ ∀ q < List.idxOf x s, s[q]! ≠ x := by
        intros x hx; exact ⟨by
        exact?, by
          simp +decide [ hx, List.getElem?_eq_getElem ], by
          intro q hq; by_contra h_contra; have := List.idxOf_lt_length_iff.mpr hx; simp_all +decide [ List.getElem?_eq_getElem ] ;
          have h_first_occurrence : ∀ {l : List ℤ} {x : ℤ} {q : ℕ}, q < List.idxOf x l → l[q]?.getD 0 ≠ x := by
            intros l x q hq; induction' l with hd tl ih generalizing q <;> simp_all +decide [ List.idxOf_cons ] ;
            grind +ring;
          exact h_first_occurrence hq h_contra⟩;
      exact h_first_occurrence _ ( h_elements _ |>.1 ( by simp [ hi ] ) )
    have h_order : ∀ i j, i < j → j < result.length → ∃ pi pj, LLMSpec.FirstOccurrenceAt result[i]! s pi ∧ LLMSpec.FirstOccurrenceAt result[j]! s pj ∧ pi < pj := by
      intro i j hij hj
      obtain ⟨pi, hpi⟩ := h_first_occurrence i (by linarith)
      obtain ⟨pj, hpj⟩ := h_first_occurrence j (by linarith);
      have h_pairwise : List.idxOf result[i]! s < List.idxOf result[j]! s := by
        have := List.pairwise_iff_get.mp h.2.2.2;
        convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij _;
        · grind;
        · grind;
        · simp +decide [ List.idxOf_get ];
          rw [ List.idxOf_getElem, List.idxOf_getElem ] <;> aesop;
      -- By definition of `FirstOccurrenceAt`, we know that `pi` and `pj` are the indices where `result[i]!` and `result[j]!` appear first in `s`.
      have h_pi_pj : pi = List.idxOf result[i]! s ∧ pj = List.idxOf result[j]! s := by
        have h_pi_pj : ∀ x p, LLMSpec.FirstOccurrenceAt x s p → p = List.idxOf x s := by
          intros x p hp
          obtain ⟨hp_lt, hp_eq, hp_unique⟩ := hp
          have h_idx : List.idxOf x s = p := by
            refine' le_antisymm _ _ <;> contrapose! hp_unique;
            · have h_idx : List.idxOf x s ≤ p := by
                have h_idx : ∀ {l : List ℤ} {x : ℤ} {p : ℕ}, p < l.length → l[p]! = x → List.idxOf x l ≤ p := by
                  -- By definition of `List.idxOf`, if `p` is the position of `x` in `l`, then `List.idxOf x l ≤ p`.
                  intros l x p hp_lt hp_eq
                  induction' l with hd tl ih generalizing p x
                  all_goals simp_all +decide [ List.idxOf_cons ];
                  grind;
                exact h_idx hp_lt hp_eq;
              linarith;
            · aesop
          exact h_idx.symm;
        exact ⟨ h_pi_pj _ _ hpi, h_pi_pj _ _ hpj ⟩;
      exact ⟨ pi, pj, hpi, hpj, by linarith ⟩
    exact ⟨h_nodup, h_elements, h_first_occurrence, h_order⟩;
  · intro h_postcond
    obtain ⟨h_nodup, h_eq, h_first, h_incr⟩ := h_postcond
    have h_unique : result.Nodup := h_nodup
    have h_subset : ∀ x, x ∈ result ↔ x ∈ s := h_eq
    have h_seq : List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result := by
      have h_seq : ∀ i j : ℕ, i < j → j < result.length → List.idxOf result[i]! s < List.idxOf result[j]! s := by
        intros i j hij hj_lt
        obtain ⟨pi, pj, hpi, hpj, hpi_lt_pj⟩ := h_incr i j hij hj_lt
        have hpi_eq : pi = List.idxOf result[i]! s := by
          obtain ⟨hpi_lt, hpi_eq, hpi_unique⟩ := hpi
          have hpi_eq : pi = List.idxOf result[i]! s := by
            refine' le_antisymm _ _ <;> simp_all +decide [ List.idxOf ];
            · grind +ring;
            · grind +ring
          exact hpi_eq.symm ▸ rfl
        have hpj_eq : pj = List.idxOf result[j]! s := by
          obtain ⟨ hpj_lt, hpj_eq, hpj_lt' ⟩ := hpj;
          refine' le_antisymm _ _ <;> simp_all +decide [ List.idxOf ];
          · grind +ring;
          · grind
        rw [hpi_eq, hpj_eq] at hpi_lt_pj
        exact hpi_lt_pj;
      -- By definition of pairwise, we need to show that for any i < j in the result list, the indices of the elements in s are increasing.
      apply List.pairwise_iff_get.mpr;
      -- Since the indices in the result list are the same as the indices in the result list, and the indices in s are determined by the first occurrence, the pairwise condition holds.
      intros i j hij hidx
      have h_lt : i.val < j.val := by
        exact hij
      have h_lt_s : List.idxOf (result.get i) s < List.idxOf (result.get j) s := by
        convert h_seq i j h_lt ( by simp ) using 1 <;> simp +decide [ List.get ]
      exact h_lt_s
    exact ⟨by
    aesop, by
      grind +ring, by
      simp_all +decide [ List.count_eq_one_of_mem ], h_seq⟩

end Proof