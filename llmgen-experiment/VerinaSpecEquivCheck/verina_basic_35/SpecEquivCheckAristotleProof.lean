/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4616ec8e-1ca5-462e-a2ef-af2c30100a3a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (arr : Array Int) : VerinaSpec.MoveZeroesToEnd_precond arr ↔ LLMSpec.precondition arr

- theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.MoveZeroesToEnd_postcond arr result ↔ LLMSpec.postcondition arr result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  True

def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)

end VerinaSpec

namespace LLMSpec

-- Helper: count of non-zero elements.
-- We use Bool predicates for computable counting via `Array.countP`.
def nonZeroCount (arr : Array Int) : Nat :=
  arr.countP (fun x => x != 0)

-- Helper: the number of non-zero elements strictly before index `i`.
-- This is the “rank” of the element at `i` among non-zero elements.
def nzRank (arr : Array Int) (i : Nat) : Nat :=
  (arr.take i).countP (fun x => x != 0)

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- Size is preserved.
  result.size = arr.size ∧
  -- The number of zeros is preserved.
  result.countP (fun x => x == 0) = arr.countP (fun x => x == 0) ∧
  -- Zeros form a suffix (all indices at/after `k` are 0, and before `k` are non-zero).
  (let k := nonZeroCount arr
   (∀ i : Nat, i < k → result[i]! ≠ 0) ∧
   (∀ i : Nat, k ≤ i → i < result.size → result[i]! = 0)) ∧
  -- Stability for non-zero elements:
  -- For every non-zero element at position `j` in the input, it appears in the output at
  -- index `nzRank arr j`.
  (∀ j : Nat, j < arr.size → arr[j]! ≠ 0 →
    (let r := nzRank arr j
     r < result.size ∧ result[r]! = arr[j]!)) ∧
  -- Coverage of all non-zero output positions:
  -- Every index in the non-zero prefix corresponds to some non-zero element of the input
  -- with the same rank.
  (let k := nonZeroCount arr
   ∀ i : Nat, i < k →
     ∃ j : Nat, j < arr.size ∧ arr[j]! ≠ 0 ∧ nzRank arr j = i ∧ result[i]! = arr[j]!)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) : VerinaSpec.MoveZeroesToEnd_precond arr ↔ LLMSpec.precondition arr := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.MoveZeroesToEnd_precond, LLMSpec.precondition]

noncomputable section AristotleLemmas

/-
The target list is the concatenation of the non-zero elements of the input array and the zero elements of the input array.
-/
def VerinaSpec.target (arr : Array Int) : List Int :=
  arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0)

/-
VerinaSpec's postcondition is equivalent to saying the result list is exactly the target list (non-zeros followed by zeros).
-/
theorem VerinaSpec_equiv_target (arr : Array Int) (result : Array Int) :
  VerinaSpec.MoveZeroesToEnd_postcond arr result ↔ result.toList = VerinaSpec.target arr := by
  constructor <;> intro h;
  · unfold VerinaSpec.MoveZeroesToEnd_postcond VerinaSpec.target at *;
    rw [ ← h.2.1, ← h.2.2, List.take_append_drop ];
  · constructor;
    · rw [ List.isPerm_iff ];
      rw [ List.perm_iff_count ];
      intro a; by_cases ha : a = 0 <;> simp +decide [ *, VerinaSpec.target ] ;
      · rw [ List.count_eq_zero ] ; aesop;
      · rw [ List.count_eq_zero ] ; aesop;
    · by_cases h : 0 ∈ arr.toList.filter ( · ≠ 0 ) <;> simp_all +decide [ List.idxOf_append ];
      unfold VerinaSpec.target; simp +decide [ List.idxOf_append, List.filter_eq ] ;
      rcases n : Array.count 0 arr with ( _ | _ | n ) <;> simp_all +decide [ List.replicate ]

/-
LLMSpec's postcondition is equivalent to saying the result list is exactly the target list.
-/
theorem LLMSpec_equiv_target (arr : Array Int) (result : Array Int) :
  LLMSpec.postcondition arr result ↔ result.toList = VerinaSpec.target arr := by
  -- To prove the equivalence, we show that the target list satisfies all the conditions of LLMSpec.postcondition.
  have h_target : LLMSpec.postcondition arr (Array.mk (VerinaSpec.target arr)) := by
    refine' ⟨ _, _, _, _, _ ⟩;
    · simp +decide [ VerinaSpec.target ];
      induction arr ; simp +decide [ * ];
      induction ‹List ℤ› <;> simp +decide [ * ] ;
      grind;
    · unfold VerinaSpec.target; simp +decide [ List.filter_eq, List.countP_eq_length_filter ] ;
      rw [ List.filter_eq_nil_iff.mpr ] <;> aesop;
    · unfold LLMSpec.nonZeroCount VerinaSpec.target; simp +decide ;
      grind;
    · unfold LLMSpec.nzRank VerinaSpec.target;
      induction' arr using Array.recOn with arr ih ; simp_all +decide [ Array.countP ];
      induction' arr with a arr ih <;> simp_all +decide [ List.take ];
      intro j hj hj'; rcases j with ( _ | j ) <;> simp_all +decide [ List.take ] ;
      grind +ring;
    · unfold LLMSpec.nonZeroCount LLMSpec.nzRank VerinaSpec.target;
      intro k hk;
      induction' arr using Array.recOn with x xs ih;
      induction' x using List.reverseRecOn with x xs ih;
      · aesop;
      · by_cases h : xs = 0 <;> simp_all +decide [ Array.countP_append ];
        · intro hk'; obtain ⟨ j, hj₁, hj₂, hj₃, hj₄ ⟩ := ih ( by aesop ) ; use j; simp_all +decide [ List.getElem?_append ] ;
          rw [ List.take_append_of_le_length ] <;> simp_all +decide [ List.countP_append ];
          · grind;
          · linarith;
        · intro hk_lt_k
          by_cases hk_lt_count : hk < List.countP (fun x => x != 0) x;
          · obtain ⟨ j, hj₁, hj₂, hj₃, hj₄ ⟩ := ih hk_lt_count; use j; simp_all +decide [ List.getElem_append ] ;
            simp_all +decide [ List.getElem?_append, List.take_append_of_le_length, hj₁.le ];
            grind;
          · use x.length;
            simp_all +decide [ List.take_append, List.countP_append ];
            grind;
  constructor <;> intro h;
  · have := h.2.2.1.1; have := h.2.2.1.2; have := h.2.2.2.1; have := h.2.2.2.2; have := h_target.2.2.1.1; have := h_target.2.2.1.2; have := h_target.2.2.2.1; have := h_target.2.2.2.2; simp_all +decide [ List.take_append_of_le_length, List.drop_append_of_le_length ] ;
    refine' List.ext_get _ _ <;> simp_all +decide [ List.get ];
    · exact h.1.trans h_target.1.symm;
    · grind +ring;
  · cases result ; aesop

end AristotleLemmas

theorem postcondition_equiv (arr : Array Int) (result : Array Int) : LLMSpec.precondition arr →
  (VerinaSpec.MoveZeroesToEnd_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  exact fun h => by rw [VerinaSpec_equiv_target, LLMSpec_equiv_target];

end Proof