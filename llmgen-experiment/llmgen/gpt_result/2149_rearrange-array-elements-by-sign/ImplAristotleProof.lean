import Mathlib

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    2149. Rearrange Array Elements by Sign: Rearrange an even-length integer array with equal numbers of positive and negative elements so that signs alternate starting with a positive, while preserving relative order within each sign.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input is a 0-indexed array of integers of even length.
    2. Every element is either strictly positive or strictly negative (no zeros).
    3. The number of positive elements equals the number of negative elements.
    4. The output is an array of the same length that is a rearrangement (permutation) of the input.
    5. The output starts with a positive element when the array is nonempty.
    6. Consecutive elements in the output have opposite signs (equivalently, indices with even parity are positive and odd parity are negative).
    7. Among all positives (respectively negatives), their relative order in the output is the same as in the input (stable with respect to sign).
-/

section Specs
-- Helper predicates as Bool for use with Array.filter/countP.
def isPosB (x : Int) : Bool := decide (x > 0)
def isNegB (x : Int) : Bool := decide (x < 0)

def countPos (nums : Array Int) : Nat := nums.countP isPosB

def countNeg (nums : Array Int) : Nat := nums.countP isNegB

def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

-- Parity-based sign pattern for the desired result.
def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

-- Stable order within sign can be characterized by equality of the sign-filtered subsequences.
def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

-- Preconditions: even length, no zeros, equal number of positives and negatives.
def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

-- Postconditions: permutation, correct alternating sign pattern, starts with positive if nonempty,
-- and stability of relative order within each sign.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result
end Specs

section TestCases
-- Test case 1: Example 1
-- Input: [3,1,-2,-5,2,-4]
-- Output: [3,-2,1,-5,2,-4]
def test1_nums : Array Int := #[3, 1, -2, -5, 2, -4]
def test1_Expected : Array Int := #[3, -2, 1, -5, 2, -4]

-- Test case 2: Example 2 (starts with a negative in input)
def test2_nums : Array Int := #[-1, 1]
def test2_Expected : Array Int := #[1, -1]

-- Test case 3: Empty array (degenerate but satisfies even length and equal counts)
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Smallest nontrivial already-correct alternating order
def test4_nums : Array Int := #[1, -1]
def test4_Expected : Array Int := #[1, -1]

-- Test case 5: Larger array where positives/negatives are grouped
-- Positives: [1,2,3], Negatives: [-1,-2,-3]
def test5_nums : Array Int := #[1, 2, 3, -1, -2, -3]
def test5_Expected : Array Int := #[1, -1, 2, -2, 3, -3]

-- Test case 6: Alternating input but begins with negative; must start with positive in output
-- Positives: [5,6], Negatives: [-5,-6]
def test6_nums : Array Int := #[-5, 5, -6, 6]
def test6_Expected : Array Int := #[5, -5, 6, -6]

-- Test case 7: Mixed order; checks stability within each sign
-- Positives in input: [2,4,6,8], Negatives: [-1,-3,-5,-7]
def test7_nums : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]
def test7_Expected : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]

-- Test case 8: All positives first but with different magnitudes; confirms stable order
-- Positives: [10,1,7], Negatives: [-2,-9,-3]
def test8_nums : Array Int := #[10, 1, 7, -2, -9, -3]
def test8_Expected : Array Int := #[10, -2, 1, -9, 7, -3]
end TestCases

section Proof

/-
PROVIDED SOLUTION
The key idea: We know that `invariant_interleave_prefix` tells us that for all k < i_4, even-indexed positions of res_1 contain the positive elements from nums (in order), and odd-indexed positions contain negative elements. Since `hi4 : i_4 = nums.size` and `invariant_interleave_res_size : res_1.size = nums.size`, the prefix covers the entire array.

To prove `Array.filter isPosB res_1 = Array.filter isPosB nums`, we need to show that the positive elements of res_1 (in order) are the same as the positive elements of nums.

From `invariant_interleave_prefix`, for even k, `res_1[k]! = (Array.filter isPosB nums)[k/2]!`, and for odd k, `res_1[k]! = (Array.filter isNegB nums)[k/2]!`. The negative elements satisfy `isNegB` (they are negative), so `isPosB` is false for them. The positive elements satisfy `isPosB`.

So filtering res_1 by isPosB picks out exactly the even-indexed elements (which are the positive filter of nums), preserving order. This gives us `Array.filter isPosB res_1 = Array.filter isPosB nums`.

This is a complex array reasoning problem. An alternative approach: try using the collect invariants directly. We have `invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract 0 i_1) 0 (min i_1 nums.size)` and `done_1 : nums.size ≤ i_1`, so `nums.extract 0 i_1 = nums` (since i_1 ≥ nums.size). This might simplify things.

Actually, a much simpler approach might work: this is fundamentally about array operations and may require induction or careful unfolding. The subagent should try `simp` with relevant lemmas, `ext`, or unfold definitions and work with the filter characterization.
-/
theorem goal_8_0_0 (nums : Array ℤ) (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2) (i_1 : ℕ) (i_4 : ℕ) (res_1 : Array ℤ) (invariant_collect_bounds : i_1 ≤ nums.size) (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2) (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2) (invariant_interleave_bounds : i_4 ≤ nums.size) (invariant_interleave_res_size : res_1.size = nums.size) (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)) (done_1 : nums.size ≤ i_1) (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)) (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)) (done_2 : nums.size ≤ i_4) (hi4 : i_4 = nums.size) (h_alt : alternatesStartingPos res_1) (h_start : res_1.size > 0 → res_1[0]! > 0) : Array.filter isPosB res_1 = Array.filter isPosB nums := by
    ext i;
    · have h_filter_eq : (Array.filter isPosB res_1).size = (Finset.filter (fun i => res_1[i]! > 0) (Finset.range res_1.size)).card := by
        have h_filter_eq : ∀ (arr : Array ℤ), (Array.filter isPosB arr).size = (Finset.filter (fun i => arr[i]! > 0) (Finset.range arr.size)).card := by
          intro arr; induction arr using Array.recOn ; simp +decide [ *, Finset.sum_range_succ ] ;
          induction ‹List ℤ› <;> simp +decide [ *, Finset.sum_range_succ' ];
          rw [ Finset.card_filter ];
          rw [ Finset.sum_range_succ' ] ; simp +decide [ *, List.filter_cons ];
          split_ifs <;> simp_all +decide [ isPosB ];
        apply h_filter_eq;
      rw [ h_filter_eq, Finset.card_eq_of_bijective ];
      use fun i hi => 2 * i;
      · grind +locals;
      · simp +zetaDelta at *;
        exact fun i hi => ⟨ by linarith [ Nat.div_mul_le_self nums.size 2 ], h_alt ( 2 * i ) ( by linarith [ Nat.div_mul_le_self nums.size 2 ] ) |>.1 ( by norm_num ) ⟩;
      · aesop;
    · have h_filter_eq : Array.filter isPosB res_1 = Array.map (fun k => res_1[2 * k]!) (Array.range (nums.size / 2)) := by
        have h_filter_eq : ∀ (arr : Array ℤ), alternatesStartingPos arr → arr.size % 2 = 0 → Array.filter isPosB arr = Array.map (fun k => arr[2 * k]!) (Array.range (arr.size / 2)) := by
          intro arr h_alt h_even
          have h_filter_eq : ∀ (n : ℕ), n ≤ arr.size / 2 → Array.filter isPosB (arr.take (2 * n)) = Array.map (fun k => arr[2 * k]!) (Array.range n) := by
            intro n hn;
            induction' n with n ih;
            · grind +splitIndPred;
            · have := h_alt ( 2 * n ) ( by linarith [ Nat.div_mul_le_self arr.size 2 ] ) ; have := h_alt ( 2 * n + 1 ) ( by linarith [ Nat.div_mul_le_self arr.size 2 ] ) ; simp_all +decide [ Nat.add_mod, Nat.mul_succ ] ;
              rw [ show arr.extract 0 ( 2 * n + 2 ) = arr.extract 0 ( 2 * n ) ++ #[arr[2 * n]!, arr[2 * n + 1]!] from ?_ ];
              · grind +locals;
              · ext i ; simp +decide [ Array.getElem?_append, Array.getElem?_extract ];
                · grind;
                · simp +zetaDelta at *;
                  grind;
          convert h_filter_eq ( arr.size / 2 ) le_rfl using 1;
          norm_num [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero h_even ) ];
        rw [ h_filter_eq res_1 h_alt, invariant_interleave_res_size ];
        exact invariant_interleave_res_size.symm ▸ Nat.mod_eq_zero_of_dvd ( Nat.dvd_of_mod_eq_zero ( by simpa using require_1.1 ) );
      simp_all +decide [ Nat.mul_div_assoc ];
      grind

/-
PROVIDED SOLUTION
Similar to goal_8_0_0 but for negative elements. The invariant_interleave_prefix tells us odd-indexed positions of res_1 contain negative elements from nums filter. Filtering res_1 by isNegB picks out exactly those, giving Array.filter isNegB res_1 = Array.filter isNegB nums.

Same approach as goal_8_0_0 should work.
-/
theorem goal_8_0_1 (nums : Array ℤ) (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2) (i_1 : ℕ) (i_4 : ℕ) (res_1 : Array ℤ) (invariant_collect_bounds : i_1 ≤ nums.size) (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2) (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2) (invariant_interleave_bounds : i_4 ≤ nums.size) (invariant_interleave_res_size : res_1.size = nums.size) (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)) (done_1 : nums.size ≤ i_1) (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)) (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)) (done_2 : nums.size ≤ i_4) (hi4 : i_4 = nums.size) (h_alt : alternatesStartingPos res_1) (h_start : res_1.size > 0 → res_1[0]! > 0) (hpos : Array.filter isPosB res_1 = Array.filter isPosB nums) : Array.filter isNegB res_1 = Array.filter isNegB nums := by
    refine' Array.ext _ _ <;> simp +decide [ hi4, invariant_interleave_prefix ] at *;
    · have h_len_eq : (Array.filter isPosB res_1).size + (Array.filter isNegB res_1).size = res_1.size ∧ (Array.filter isPosB nums).size + (Array.filter isNegB nums).size = nums.size := by
        have h_count : ∀ (arr : Array ℤ), (∀ i < arr.size, arr[i]! ≠ 0) → (Array.filter isPosB arr).size + (Array.filter isNegB arr).size = arr.size := by
          intro arr harr; induction arr using Array.recOn ; simp_all +decide [ Array.filter ] ;
          induction' ‹List ℤ› using List.reverseRecOn with a l ih <;> simp_all +decide [ isPosB, isNegB ];
          split_ifs <;> simp_all +decide [ List.length_append ];
          · exact absurd ‹_› ( not_lt_of_gt ‹_› );
          · linarith [ ih fun i hi => harr i ( by linarith ) |> fun h => by simpa [ List.getElem_append_right, hi ] using h ];
          · linarith [ ih fun i hi => harr i ( by linarith ) |> fun h => by simpa [ List.getElem_append_right, hi ] using h ];
          · exact absurd ( harr ( a.length ) ( by linarith ) ) ( by norm_num; linarith );
        apply And.intro (h_count res_1 (by
        intro i hi; specialize h_alt i hi; rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp_all +decide ;
        · exact ne_of_gt h_alt;
        · exact ne_of_lt h_alt)) (h_count nums (by
        exact require_1.2.1))
      generalize_proofs at *; (
      grind);
    · -- Since `res_1` is a permutation of `nums`, the index positions in `res_1` correspond to the same positions in `nums`.
      intro k hk₁ hk₂
      have := invariant_interleave_prefix (2 * k + 1) (by
      grind +ring);
      norm_num [ Nat.add_mod, Nat.mul_mod, Nat.add_div ] at this;
      convert this using 1;
      · -- Since the negative elements in `res_1` are exactly the elements at odd indices, the k-th negative element in `res_1` is the element at position `2k+1`.
        have h_neg_pos : ∀ k < (Array.filter isNegB res_1).size, (Array.filter isNegB res_1)[k]! = res_1[2 * k + 1]! := by
          intros k hk₁
          have h_neg_pos : ∀ i < res_1.size, (isNegB res_1[i]!) = (i % 2 = 1) := by
            intro i hi; specialize h_alt i hi; rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp_all +decide ;
            · grind +locals;
            · exact decide_eq_true ( by simpa using h_alt );
          have h_neg_pos : ∀ (l : List ℤ), (∀ i < l.length, (isNegB l[i]!) = (i % 2 = 1)) → ∀ k < (List.filter isNegB l).length, (List.filter isNegB l)[k]! = l[2 * k + 1]! := by
            intros l hl k hk₁; induction' k with k ih generalizing l <;> simp_all +decide [ Nat.mul_succ, List.filter_cons ] ;
            · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ List.filter_cons ];
              have := hl 0; have := hl 1; simp_all +decide ;
            · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ, List.filter_cons ];
              have := hl 0; have := hl 1; simp_all +decide ;
              convert ih l _ hk₁ using 1;
              exact fun i hi => by simpa using hl ( i + 2 ) ( by linarith ) ;
          cases res_1 ; aesop;
        grind;
      · grind

/-
PROVIDED SOLUTION
We have `h_stable : stableBySign nums res_1` which unfolds to `result.filter isPosB = nums.filter isPosB ∧ result.filter isNegB = nums.filter isNegB`. We also have `invariant_interleave_res_size : res_1.size = nums.size` and `h_alt : alternatesStartingPos res_1`.

To show res_1.Perm nums (as arrays/lists), we need to show they are permutations.

Key insight: every element of nums is either positive or negative (from require_1, allNonZero). So nums is the interleaving of its positive and negative filters, and similarly for res_1. If both filters match, the multisets of elements must match, giving a permutation.

More concretely: For any value v, the count of v in res_1 equals count of v in (filter isPosB res_1) + count of v in (filter isNegB res_1) (since every element is positive or negative). Since both filters equal the corresponding filters of nums, the counts match, proving permutation.

Try using `Array.Perm` or converting to lists and using `List.Perm`. The proof might use `List.perm_iff_count` or multiset reasoning.
-/
theorem goal_8_1 (nums : Array ℤ) (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2) (i_1 : ℕ) (i_4 : ℕ) (res_1 : Array ℤ) (invariant_collect_bounds : i_1 ≤ nums.size) (invariant_interleave_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2) (invariant_interleave_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2) (invariant_interleave_bounds : i_4 ≤ nums.size) (invariant_interleave_res_size : res_1.size = nums.size) (invariant_interleave_prefix : ∀ k < i_4,
  (k % OfNat.ofNat 2 = OfNat.ofNat 0 → res_1[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!) ∧
    (k % OfNat.ofNat 2 = OfNat.ofNat 1 → res_1[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)) (done_1 : nums.size ≤ i_1) (invariant_collect_neg : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)) (invariant_collect_pos : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)) (done_2 : nums.size ≤ i_4) (hi4 : i_4 = nums.size) (h_alt : alternatesStartingPos res_1) (h_start : res_1.size > 0 → res_1[0]! > 0) (h_stable : stableBySign nums res_1) : res_1.Perm nums := by
    have h_perm : ∀ v : ℤ, (res_1.filter (fun x => x = v)).size = (nums.filter (fun x => x = v)).size := by
      intro v
      by_cases hv : v > 0;
      · convert congr_arg ( fun x : Array ℤ => x.countP ( fun y => y = v ) ) h_stable.1 using 1;
        · simp +decide [ Array.countP_eq_size_filter ];
          grind +locals;
        · rw [ Array.countP_eq_size_filter ];
          rw [ Array.filter_filter ];
          congr! 2;
          ext x; by_cases hx : x = v <;> simp +decide [ hx, hv ] ;
          exact decide_eq_true hv;
      · by_cases hv : v < 0;
        · have h_filter_eq : (res_1.filter (fun x => x = v)) = (res_1.filter isNegB).filter (fun x => x = v) ∧ (nums.filter (fun x => x = v)) = (nums.filter isNegB).filter (fun x => x = v) := by
            simp +decide [ Array.filter_filter, hv ];
            grind +locals;
          rw [ h_filter_eq.1, h_filter_eq.2, h_stable.2 ];
        · have h_zero : ∀ x ∈ res_1, x ≠ 0 := by
            intro x hx; have := h_alt; simp_all +decide [ alternatesStartingPos ] ;
            obtain ⟨ k, hk ⟩ := Array.mem_iff_getElem.mp hx;
            grind +ring;
          have h_zero : ∀ x ∈ nums, x ≠ 0 := by
            intro x hx; obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp hx; aesop;
          simp_all +decide [ show v = 0 by linarith ];
          have h_zero : ∀ {arr : Array ℤ}, (∀ x ∈ arr, x ≠ 0) → (Array.filter (fun x => x = 0) arr).size = 0 := by
            intros arr harr; induction arr using Array.recOn ; aesop;
          convert h_zero ‹∀ x ∈ res_1, ¬x = 0› using 1;
          · grind;
          · exact h_zero ‹_›;
    have h_perm : ∀ v : ℤ, List.count v (res_1.toList) = List.count v (nums.toList) := by
      intro v; specialize h_perm v; simp_all +decide [ Array.filter_eq, List.count ] ;
      grind +ring;
    rw [ Array.perm_iff_toList_perm ];
    grind

end Proof