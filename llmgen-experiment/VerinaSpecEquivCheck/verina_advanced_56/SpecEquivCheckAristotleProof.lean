/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ab0173b6-cb5e-4a94-b71c-79a4d7592893

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) : VerinaSpec.moveZeroes_precond xs ↔ LLMSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : List Int) : LLMSpec.precondition xs →
  (VerinaSpec.moveZeroes_postcond xs result ↔ LLMSpec.postcondition xs result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def moveZeroes_precond (xs : List Int) : Prop :=
  True

def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt

def moveZeroes_postcond (xs : List Int) (result: List Int) : Prop :=
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧
  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧
  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length

end VerinaSpec

namespace LLMSpec

-- Helper: Bool predicate for “is non-zero” (for use with List.filter).
def isNonZeroB (x : Int) : Bool := x != 0

-- Helper: Bool predicate for “is zero” (for use with List.filter).
def isZeroB (x : Int) : Bool := x == 0

-- No input restrictions.
def precondition (xs : List Int) : Prop :=
  True

-- Property-based stable partition specification:
-- (a) length preserved
-- (b) all zeros are at the end (zeros form a suffix)
-- (c) multiset preserved via element counts
-- (d) order of non-zero elements preserved (as filtered subsequence equality)
def postcondition (xs : List Int) (result : List Int) : Prop :=
  result.length = xs.length ∧
  (∀ (i : Nat) (j : Nat), i < j → j < result.length → result[i]! = 0 → result[j]! = 0) ∧
  (∀ (x : Int), result.count x = xs.count x) ∧
  (result.filter isNonZeroB) = (xs.filter isNonZeroB)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) : VerinaSpec.moveZeroes_precond xs ↔ LLMSpec.precondition xs := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.moveZeroes_precond, LLMSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : List Int) : LLMSpec.precondition xs →
  (VerinaSpec.moveZeroes_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  intro h_pre
  constructor;
  · intro h_post
    obtain ⟨h_subseq, h_zeros, h_count, h_length⟩ := h_post
    simp [LLMSpec.postcondition, h_subseq, h_zeros, h_count, h_length];
    refine' ⟨ _, _, _ ⟩;
    · intro i j hij hj h_zero_i
      have h_zero_j : ∀ k, i < k → k < result.length → result[k]?.getD 0 = 0 := by
        intros k hk_i hk_j
        have h_zero_j : ∀ {l : List ℤ}, (List.dropWhile (fun x => x ≠ 0) l).all (fun x => x = 0) → ∀ {i j : ℕ}, i < j → j < l.length → l[i]?.getD 0 = 0 → l[j]?.getD 0 = 0 := by
          intros l hl i j hij hj h_zero_i
          induction' l with x l ih generalizing i j;
          · contradiction;
          · rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide;
            by_cases hx : x = 0 <;> simp_all +decide [ List.dropWhile ];
            · exact hl _ ( by simp );
            · exact ih hl hij hj h_zero_i;
        exact h_zero_j h_zeros hk_i hk_j h_zero_i
      exact h_zero_j j hij hj;
    · intro x; by_cases hx : x = 0 <;> simp_all +decide [ List.count ] ;
      · convert h_count.symm using 1;
        · -- By definition of `countVal`, we know that `countVal 0 result` is the number of zeros in `result`.
          have h_countVal : ∀ (xs : List ℤ), VerinaSpec.countVal 0 xs = List.countP (fun x => x == 0) xs := by
            intro xs; induction xs <;> simp +decide [ *, List.countP_cons ] ;
            split_ifs <;> simp_all +decide [ VerinaSpec.countVal ];
          rw [ h_countVal ];
        · -- By definition of `countVal`, we have that `countVal 0 xs` is the number of zeros in `xs`.
          have h_countVal : ∀ (xs : List ℤ), VerinaSpec.countVal 0 xs = List.count 0 xs := by
            intro xs; induction xs <;> simp +decide [ *, VerinaSpec.countVal ] ;
            split_ifs <;> simp +decide [ *, List.count_cons ];
          rw [ h_countVal, List.count ];
      · have h_count_eq : List.countP (fun x_1 => x_1 == x) result = List.countP (fun x_1 => x_1 == x) (result.filter (fun x_1 => x_1 ≠ 0)) := by
          rw [ List.countP_filter ];
          exact List.countP_congr fun y hy => by aesop;
        have h_count_eq : List.countP (fun x_1 => x_1 == x) (List.filter (fun x_1 => x_1 ≠ 0) result) = List.countP (fun x_1 => x_1 == x) (List.filter (fun x_1 => x_1 ≠ 0) xs) := by
          have h_count_eq : List.Sublist (List.filter (fun x_1 => x_1 ≠ 0) xs) (List.filter (fun x_1 => x_1 ≠ 0) result) := by
            have h_subseq : ∀ {xs ys : List ℤ}, VerinaSpec.isSubsequence xs ys = Bool.true → List.Sublist xs ys := by
              intros xs ys h_subseq; induction' xs with x xs ih generalizing ys <;> induction' ys with y ys ih' <;> simp_all +decide [ List.Sublist ] ;
              · cases h_subseq;
              · by_cases hxy : x = y <;> simp_all +decide [ VerinaSpec.isSubsequence ];
            convert h_subseq ‹_› |> List.Sublist.filter _ using 1 ; aesop;
          have h_count_eq : List.length (List.filter (fun x_1 => x_1 ≠ 0) xs) = List.length (List.filter (fun x_1 => x_1 ≠ 0) result) := by
            have h_count_eq : List.length (List.filter (fun x_1 => x_1 ≠ 0) xs) = List.length xs - List.length (List.filter (fun x_1 => x_1 = 0) xs) := by
              rw [ tsub_eq_of_eq_add_rev ];
              rw [ List.length_eq_countP_add_countP ];
              rw [ List.countP_eq_length_filter ];
              rw [ List.countP_eq_length_filter ] ; aesop
            have h_count_eq' : List.length (List.filter (fun x_1 => x_1 ≠ 0) result) = List.length result - List.length (List.filter (fun x_1 => x_1 = 0) result) := by
              rw [ tsub_eq_of_eq_add_rev ];
              rw [ List.length_eq_countP_add_countP ];
              rw [ List.countP_eq_length_filter ];
              rw [ List.countP_eq_length_filter ] ; aesop
            simp_all +decide [ List.filter_eq ];
            have h_count_eq : ∀ (xs : List ℤ), List.count 0 xs = VerinaSpec.countVal 0 xs := by
              intro xs; induction xs <;> simp +decide [ *, List.count_cons ] ;
              split_ifs <;> simp +decide [ *, VerinaSpec.countVal ];
            rw [ h_count_eq, h_count_eq, h_count ];
          grind;
        convert h_count_eq using 1;
        rw [ List.countP_filter ];
        exact List.countP_congr fun y hy => by aesop;
    · -- By definition of `isSubsequence`, if `VerinaSpec.isSubsequence (List.filter (fun x => x ≠ 0) xs) result = Bool.true`, then `List.filter (fun x => x ≠ 0) xs` is a subsequence of `result`.
      have h_subseq_nonzero : List.Sublist (List.filter (fun x => x ≠ 0) xs) result := by
        have h_subseq_nonzero : ∀ {xs ys : List ℤ}, VerinaSpec.isSubsequence xs ys = Bool.true → List.Sublist xs ys := by
          intros xs ys h_subseq; induction' xs with x xs ih generalizing ys <;> induction' ys with y ys ih' <;> simp_all +decide [ List.Sublist ] ;
          · cases h_subseq;
          · by_cases h : x = y <;> simp_all +decide [ VerinaSpec.isSubsequence ];
        exact h_subseq_nonzero h_subseq;
      have h_subseq_nonzero : List.Sublist (List.filter (fun x => x ≠ 0) xs) (List.filter (fun x => x ≠ 0) result) := by
        have h_subseq_nonzero : List.Sublist (List.filter (fun x => x ≠ 0) (List.filter (fun x => x ≠ 0) xs)) (List.filter (fun x => x ≠ 0) result) := by
          exact?;
        aesop;
      have h_subseq_nonzero : List.length (List.filter (fun x => x ≠ 0) xs) = List.length (List.filter (fun x => x ≠ 0) result) := by
        -- Since the length of the list is the sum of the lengths of the zeros and the non-zeros, and the total lengths are equal, the lengths of the non-zeros must be equal.
        have h_nonzero_length : List.length (List.filter (fun x => x ≠ 0) xs) = List.length xs - List.length (List.filter (fun x => x = 0) xs) ∧ List.length (List.filter (fun x => x ≠ 0) result) = List.length result - List.length (List.filter (fun x => x = 0) result) := by
          have h_nonzero_length : ∀ (l : List ℤ), List.length (List.filter (fun x => x ≠ 0) l) = List.length l - List.length (List.filter (fun x => x = 0) l) := by
            -- We can prove this by induction on the list.
            intro l
            induction' l with x l ih;
            · rfl;
            · grind;
          exact ⟨ h_nonzero_length xs, h_nonzero_length result ⟩;
        have h_count_zero : ∀ (xs : List ℤ), VerinaSpec.countVal 0 xs = List.count 0 xs := by
          intro xs; induction xs <;> simp +decide [ *, List.count_cons ] ;
          by_cases h : ‹ℤ› = 0 <;> simp +decide [ *, VerinaSpec.countVal ];
        grind +ring;
      have h_subseq_nonzero : List.Sublist (List.filter (fun x => x ≠ 0) result) (List.filter (fun x => x ≠ 0) xs) := by
        grind;
      have h_subseq_nonzero : List.Sublist (List.filter (fun x => x ≠ 0) result) (List.filter (fun x => x ≠ 0) xs) ∧ List.Sublist (List.filter (fun x => x ≠ 0) xs) (List.filter (fun x => x ≠ 0) result) := by
        aesop;
      have := List.Sublist.eq_of_length_le h_subseq_nonzero.1; aesop;
  · intro h_post
    obtain ⟨h_len, h_zeros, h_counts, h_order⟩ := h_post
    constructor;
    · -- Since the non-zero elements of `result` and `xs` are the same, we can conclude that `result.filter (fun x => x ≠ 0)` is a subsequence of `result`.
      have h_subseq : List.Sublist (result.filter (fun x => x ≠ 0)) result := by
        exact?;
      have h_subseq : ∀ {l1 l2 : List ℤ}, List.Sublist l1 l2 → VerinaSpec.isSubsequence l1 l2 = Bool.true := by
        -- We can prove this by induction on the length of `l1`.
        intro l1 l2 h_sublist
        induction' l1 with x l1 ih generalizing l2;
        · cases l2 <;> trivial;
        · induction' l2 with y l2 ih' <;> simp_all +decide [ List.sublist_cons_iff ];
          cases h_sublist <;> simp_all +decide [ VerinaSpec.isSubsequence ];
          exact Or.inr ( ih <| List.Sublist.trans ( List.sublist_cons_self _ _ ) ‹_› );
      convert h_subseq ‹_› using 1;
      congr! 1;
      convert h_order.symm using 1;
      · unfold LLMSpec.isNonZeroB; aesop;
      · unfold LLMSpec.isNonZeroB; aesop;
    · -- Since the result list has all zeros at the end, the dropWhile operation will remove all non-zero elements, leaving only zeros. Hence, the all function will return true.
      have h_dropWhile : ∀ {l : List ℤ}, (∀ i j, i < j → j < l.length → l[i]! = 0 → l[j]! = 0) → (l.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) := by
        intros l hl; induction' l with hd tl ih <;> simp_all +decide [ List.dropWhile ] ;
        by_cases h : hd = 0 <;> simp_all +decide [ List.dropWhile ];
        · -- By induction on the length of tl, we can show that all elements in tl are zero.
          have h_tl_zero : ∀ (i : ℕ), i < tl.length → tl[i]! = 0 := by
            intro i hi; specialize hl 0 ( i + 1 ) ; aesop;
          intro x hx; obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx; specialize h_tl_zero i; aesop;
        · convert ih _ using 1;
          intro i j hij a hi; specialize hl ( i + 1 ) ( j + 1 ) ( by linarith ) ( by linarith ) ; aesop;
      have h_countVal : ∀ {l : List ℤ}, VerinaSpec.countVal 0 l = List.count 0 l := by
        intros l; induction l <;> simp +decide [ *, List.count_cons ] ;
        rename_i k l ih; rw [ show VerinaSpec.countVal 0 ( k :: l ) = if k = 0 then VerinaSpec.countVal 0 l + 1 else VerinaSpec.countVal 0 l from rfl ] ; aesop;
      grind +ring

end Proof