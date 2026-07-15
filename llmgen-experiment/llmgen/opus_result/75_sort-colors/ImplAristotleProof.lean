/- This file type checks in Lean 4.28 -/

import Mathlib

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    SortColors: Given an array of colors encoded as 0, 1, 2, reorder it so that all 0s come first,
    then all 1s, then all 2s.
    Natural language breakdown:
    1. The input is an array `nums` of natural numbers that represent colors.
    2. Only the values 0, 1, and 2 are valid colors.
    3. The output must have the same length as the input.
    4. The output must contain the same multiset of elements as the input (no loss/duplication).
    5. The output must be ordered so that every 0 appears before every 1 and every 1 before every 2.
    6. Equivalently, there exist boundaries a ≤ b such that indices < a are 0, indices in [a,b) are 1,
       and indices ≥ b are 2.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

section Specs
-- Helper: all entries are in {0,1,2}
def ColorsOnly (nums : Array Nat) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≤ 2

-- Helper: array is partitioned into 0s then 1s then 2s
-- This avoids referencing any particular algorithm while fully characterizing the desired order.
def Is012Sorted (nums : Array Nat) : Prop :=
  ∃ (a : Nat) (b : Nat),
    a ≤ b ∧ b ≤ nums.size ∧
    (∀ (i : Nat), i < a → nums[i]! = 0) ∧
    (∀ (i : Nat), a ≤ i ∧ i < b → nums[i]! = 1) ∧
    (∀ (i : Nat), b ≤ i ∧ i < nums.size → nums[i]! = 2)

-- Helper: count occurrences of a value in an array
-- (Array.count is available when DecidableEq is available.)
def countVal (nums : Array Nat) (v : Nat) : Nat :=
  nums.count v

-- Preconditions: input must contain only 0/1/2.
def precondition (nums : Array Nat) : Prop :=
  ColorsOnly nums

-- Postconditions: result has same size, is ordered as 0-then-1-then-2,
-- and preserves the counts of 0,1,2 from the input.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  result.size = nums.size ∧
  Is012Sorted result ∧
  countVal result 0 = countVal nums 0 ∧
  countVal result 1 = countVal nums 1 ∧
  countVal result 2 = countVal nums 2
end Specs

section TestCases
-- Test case 1: Example 1 from the problem statement
-- Input: [2,0,2,1,1,0] Output: [0,0,1,1,2,2]
def test1_nums : Array Nat := #[2, 0, 2, 1, 1, 0]
def test1_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 2: Example 2 from the problem statement
-- Input: [2,0,1] Output: [0,1,2]
def test2_nums : Array Nat := #[2, 0, 1]
def test2_Expected : Array Nat := #[0, 1, 2]

-- Test case 3: Empty array (degenerate but valid)
def test3_nums : Array Nat := #[]
def test3_Expected : Array Nat := #[]

-- Test case 4: Singleton 0
def test4_nums : Array Nat := #[0]
def test4_Expected : Array Nat := #[0]

-- Test case 5: Singleton 1
def test5_nums : Array Nat := #[1]
def test5_Expected : Array Nat := #[1]

-- Test case 6: Singleton 2
def test6_nums : Array Nat := #[2]
def test6_Expected : Array Nat := #[2]

-- Test case 7: Already sorted with repeats
def test7_nums : Array Nat := #[0, 0, 1, 1, 2, 2]
def test7_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 8: Reverse sorted
def test8_nums : Array Nat := #[2, 2, 1, 1, 0, 0]
def test8_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 9: Mixed small (extra diversity)
def test9_nums : Array Nat := #[1, 0, 2, 0, 1]
def test9_Expected : Array Nat := #[0, 0, 1, 1, 2]

-- Recommend to validate: precondition, postcondition, SortColors
end TestCases

section Proof

/-
PROVIDED SOLUTION
From i_9, obtain res_2 = res_3 and k = i_8. Substitute res_3 := res_2 everywhere.
From done_3 (nums.size ≤ k) and a_5 (k ≤ nums.size), deduce k = nums.size.

Unfold postcondition. We need 5 things:
1. res_2.size = nums.size: directly from invariant_res_size_2
2. Is012Sorted res_2: use a = Array.count 0 nums and b = Array.count 0 nums + Array.count 1 nums.
   - a ≤ b: obvious (Nat.le_add_right)
   - b ≤ nums.size: from invariant_count_sum and Nat.le_add_right
   - indices < a are 0: invariant_zeros_final
   - indices in [a,b) are 1: invariant_ones_final
   - indices in [b, nums.size) are 2: invariant_twos_filled with k = nums.size
3-5. Count preservation (countVal res_2 v = countVal nums v for v=0,1,2): The array res_2 has exactly count_0 zeros in [0, count_0), count_1 ones in [count_0, count_0+count_1), and count_2 twos in [count_0+count_1, nums.size). Since the array has size nums.size and these segments partition [0, nums.size), the counts must match. This follows from the fact that res_2 is completely determined by invariant_zeros_final, invariant_ones_final, invariant_twos_filled (with k=nums.size), which together cover all indices. Use Array.count and the partition structure. This is the hardest part. You may need to use Array.ext_getElem? or reason about counts on subarrays.

For the count preservation, one approach: show that res_2 = Array.mkArray (count 0 nums) 0 ++ Array.mkArray (count 1 nums) 1 ++ Array.mkArray (count 2 nums) 2 using Array.ext, then compute counts on this explicit form. But this might be complex.

Alternative for count preservation: use the fact that every element of res_2 is 0, 1, or 2 (from the three invariants covering all indices), and count how many indices map to each value. The number of 0s is exactly count_0 nums (the indices < count_0), the number of 1s is count_1 (indices in [count_0, count_0+count_1)), and 2s is count_2 (indices in [count_0+count_1, nums.size)). This combined with invariant_count_sum giving count_0+count_1+count_2 = nums.size should suffice.

Actually, the simplest approach might be to just try simp/omega/aesop after unfolding postcondition, Is012Sorted, and countVal, substituting res_3 with res_2 and k with nums.size. Let the automation handle it.
-/
theorem goal_12 (nums : Array ℕ) (require_1 : ∀ i < nums.size, nums[i]! ≤ OfNat.ofNat 2) (i_4 : ℕ) (i_6 : ℕ) (res_1 : Array ℕ) (k : ℕ) (res_2 : Array ℕ) (a_5 : k ≤ nums.size) (invariant_res_size_2 : res_2.size = nums.size) (invariant_rest_zero_2 : ∀ (idx : ℕ), k ≤ idx → idx < nums.size → res_2[idx]! = OfNat.ofNat 0) (i_8 : ℕ) (res_3 : Array ℕ) (a_1 : i_4 ≤ nums.size) (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = i_4) (invariant_zeros_final : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_2[idx]! = OfNat.ofNat 0) (fst_eq : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 0) nums) (fst_eq_1 : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 1) nums) (a_4 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ k) (invariant_ones_final : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums → res_2[idx]! = OfNat.ofNat 1) (invariant_twos_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ idx → idx < k → res_2[idx]! = OfNat.ofNat 2) (fst_eq_2 : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 2) nums) (invariant_count_sum : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size) (invariant_count_sum_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size) (a_2 : Array.count (OfNat.ofNat 0) nums ≤ i_6) (a_3 : i_6 ≤ Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums) (invariant_res_size_1 : res_1.size = nums.size) (invariant_zeros_intact : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_1[idx]! = OfNat.ofNat 0) (invariant_rest_zero_1 : ∀ (idx : ℕ), i_6 ≤ idx → idx < nums.size → res_1[idx]! = OfNat.ofNat 0) (invariant_ones_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < i_6 → res_1[idx]! = OfNat.ofNat 1) (done_3 : nums.size ≤ k) (i_9 : k = i_8 ∧ res_2 = res_3) (a : True) (done_1 : nums.size ≤ i_4) (invariant_c0_final_2 : True) (invariant_c1_final_2 : True) (invariant_c2_final_2 : True) (done_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ i_6) : postcondition nums res_3 := by
    refine' ⟨ _, _, _, _, _ ⟩;
    · aesop;
    · use Array.count 0 nums, Array.count 0 nums + Array.count 1 nums;
      grind;
    · convert fst_eq using 1;
      rw [ ← i_9.2, fst_eq ];
      rw [ show res_2 = Array.replicate ( Array.count 0 nums ) 0 ++ Array.replicate ( Array.count 1 nums ) 1 ++ Array.replicate ( Array.count 2 nums ) 2 from ?_ ];
      · simp +decide [ countVal ];
        norm_num [ Array.count_replicate ];
      · grind;
    · rw [ show countVal res_3 1 = Array.count 1 res_2 from ?_, show countVal nums 1 = Array.count 1 nums from ?_ ];
      · -- By definition of `res_2`, we know that its count of 1s is equal to the count of 1s in `nums`.
        have h_count_ones : Array.count 1 res_2 = Finset.card (Finset.filter (fun idx => res_2[idx]! = 1) (Finset.range res_2.size)) := by
          have h_count_ones : ∀ (arr : Array ℕ), Array.count 1 arr = Finset.card (Finset.filter (fun idx => arr[idx]! = 1) (Finset.range arr.size)) := by
            intro arr; induction arr using Array.recOn ; simp +decide [ *, Finset.sum_range_succ ] ;
            induction ‹List ℕ› <;> simp +decide [ *, Finset.sum_range_succ' ];
            rw [ Finset.card_filter ];
            rw [ Finset.sum_range_succ' ] ; aesop;
          apply h_count_ones;
        -- By definition of `res_2`, we know that its count of 1s is equal to the count of 1s in `nums` because `res_2` is constructed by rearranging the elements of `nums`.
        have h_count_ones_eq : Finset.filter (fun idx => res_2[idx]! = 1) (Finset.range res_2.size) = Finset.Ico (Array.count (OfNat.ofNat (OfNat.ofNat 0)) nums) (Array.count (OfNat.ofNat (OfNat.ofNat 0)) nums + Array.count (OfNat.ofNat (OfNat.ofNat 1)) nums) := by
          grind;
        aesop;
      · rfl;
      · exact i_9.2 ▸ rfl;
    · rw [ show res_3 = res_2 from i_9.2.symm ];
      rw [ show countVal res_2 2 = res_2.count 2 from rfl, show countVal nums 2 = nums.count 2 from rfl ];
      rw [ show res_2 = Array.replicate ( Array.count 0 nums ) 0 ++ Array.replicate ( Array.count 1 nums ) 1 ++ Array.replicate ( Array.count 2 nums ) 2 from ?_ ];
      · simp +arith +decide [ Array.count_replicate ];
      · grind

/-
PROVIDED SOLUTION
This is identical to goal_12. Just use `exact goal_12 nums require_1 i_4 i_6 res_1 k res_2 a_5 invariant_res_size_2 invariant_rest_zero_2 i_8 res_3 a_1 invariant_total_count invariant_zeros_final fst_eq fst_eq_1 a_4 invariant_ones_final invariant_twos_filled fst_eq_2 invariant_count_sum invariant_count_sum_2 a_2 a_3 invariant_res_size_1 invariant_zeros_intact invariant_rest_zero_1 invariant_ones_filled done_3 i_9 a done_1 invariant_c0_final_2 invariant_c1_final_2 invariant_c2_final_2 done_2`
-/
theorem goal_12' (nums : Array ℕ) (require_1 : ∀ i < nums.size, nums[i]! ≤ OfNat.ofNat 2) (i_4 : ℕ) (i_6 : ℕ) (res_1 : Array ℕ) (k : ℕ) (res_2 : Array ℕ) (a_5 : k ≤ nums.size) (invariant_res_size_2 : res_2.size = nums.size) (invariant_rest_zero_2 : ∀ (idx : ℕ), k ≤ idx → idx < nums.size → res_2[idx]! = OfNat.ofNat 0) (i_8 : ℕ) (res_3 : Array ℕ) (a_1 : i_4 ≤ nums.size) (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = i_4) (invariant_zeros_final : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_2[idx]! = OfNat.ofNat 0) (fst_eq : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 0) nums) (fst_eq_1 : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 1) nums) (a_4 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ k) (invariant_ones_final : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums → res_2[idx]! = OfNat.ofNat 1) (invariant_twos_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ idx → idx < k → res_2[idx]! = OfNat.ofNat 2) (fst_eq_2 : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 2) nums) (invariant_count_sum : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size) (invariant_count_sum_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size) (a_2 : Array.count (OfNat.ofNat 0) nums ≤ i_6) (a_3 : i_6 ≤ Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums) (invariant_res_size_1 : res_1.size = nums.size) (invariant_zeros_intact : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_1[idx]! = OfNat.ofNat 0) (invariant_rest_zero_1 : ∀ (idx : ℕ), i_6 ≤ idx → idx < nums.size → res_1[idx]! = OfNat.ofNat 0) (invariant_ones_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < i_6 → res_1[idx]! = OfNat.ofNat 1) (done_3 : nums.size ≤ k) (i_9 : k = i_8 ∧ res_2 = res_3) (a : True) (done_1 : nums.size ≤ i_4) (invariant_c0_final_2 : True) (invariant_c1_final_2 : True) (invariant_c2_final_2 : True) (done_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ i_6) : postcondition nums res_3 := by
    exact i_9.2 ▸ goal_12 nums require_1 i_4 i_6 res_1 k res_2 a_5 invariant_res_size_2 invariant_rest_zero_2 i_8 res_3 a_1 invariant_total_count invariant_zeros_final fst_eq fst_eq_1 a_4 invariant_ones_final invariant_twos_filled fst_eq_2 invariant_count_sum invariant_count_sum_2 a_2 a_3 invariant_res_size_1 invariant_zeros_intact invariant_rest_zero_1 invariant_ones_filled done_3 i_9 a done_1 invariant_c0_final_2 invariant_c1_final_2 invariant_c2_final_2 done_2

end Proof
