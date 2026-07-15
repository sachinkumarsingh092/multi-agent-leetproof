import Mathlib.Tactic

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    918. Maximum Sum Circular Subarray: compute the maximum possible sum of a non-empty subarray of a circular integer array.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an integer array `nums` with length `n`.
    2. A circular subarray is determined by a start index `start` and a length `len`.
    3. The chosen elements are `nums[start], nums[(start+1) mod n], ..., nums[(start+len-1) mod n]`.
    4. The subarray must be non-empty, so `1 ≤ len`.
    5. The subarray may use each element of the underlying fixed buffer at most once, so `len ≤ n`.
    6. The output is the maximum possible sum among all valid circular subarrays.
    7. The result must be achievable by at least one valid circular subarray and must be greater than or equal to
       the sum of every valid circular subarray.
-/

section Specs
-- Helper function: sum of a circular segment of length `len`, starting at index `start`.
-- Implemented as a finite sum over indices `0 .. len-1`.
-- When `arr.size > 0`, each index `(start + i) % arr.size` is within bounds.
def circSegmentSum (arr : Array Int) (start : Nat) (len : Nat) : Int :=
  (Finset.range len).sum (fun i => arr[(start + i) % arr.size]!)

-- A (start,len) pair is valid if it picks a non-empty circular segment of length at most `n`.
def isValidCircSegment (arr : Array Int) (start : Nat) (len : Nat) : Prop :=
  arr.size > 0 ∧ start < arr.size ∧ 1 ≤ len ∧ len ≤ arr.size

-- Precondition: array must be non-empty (subarray is required to be non-empty).
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- Postcondition: `result` is the maximum circular subarray sum.
-- 1) Achievability: some valid circular segment sums exactly to `result`.
-- 2) Maximality: every valid circular segment has sum ≤ result.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (len : Nat),
      isValidCircSegment nums start len ∧ circSegmentSum nums start len = result) ∧
  (∀ (start : Nat) (len : Nat),
      isValidCircSegment nums start len → circSegmentSum nums start len ≤ result)
end Specs

section TestCases
-- Test case 1: Example 1
-- Input: nums = [1,-2,3,-2]
-- Output: 3
-- Explanation: Subarray [3] has maximum sum 3.
def test1_nums : Array Int := #[1, -2, 3, -2]
def test1_Expected : Int := 3

-- Test case 2: Example 2 (wrap-around optimal)
def test2_nums : Array Int := #[5, -3, 5]
def test2_Expected : Int := 10

-- Test case 3: Example 3 (all negative)
def test3_nums : Array Int := #[-3, -2, -3]
def test3_Expected : Int := -2

-- Test case 4: Single element (must choose that element)
def test4_nums : Array Int := #[7]
def test4_Expected : Int := 7

-- Test case 5: All positive (best is whole array)
def test5_nums : Array Int := #[2, 3, 1]
def test5_Expected : Int := 6

-- Test case 6: Wrap-around beats any linear segment
-- Best is taking last and first element: 8 + 8 = 16
def test6_nums : Array Int := #[8, -1, -3, 8]
def test6_Expected : Int := 16

-- Test case 7: Contains zeros; best sum can be 0 even with negatives present
-- E.g., choose subarray [0]
def test7_nums : Array Int := #[0, -5, 0]
def test7_Expected : Int := 0

-- Test case 8: Two elements (smallest non-trivial size)
def test8_nums : Array Int := #[-1, 2]
def test8_Expected : Int := 2

-- Test case 9: Multiple candidates; maximum is achieved by a non-wrapping segment
-- Best is [3, -1, 2] with sum 4
def test9_nums : Array Int := #[3, -1, 2, -1]
def test9_Expected : Int := 4

-- Recommend to validate: all-negative arrays, wrap-around-optimal cases, single-element arrays
end TestCases

section Proof

/-
PROVIDED SOLUTION
From the hypotheses: i ≠ 0, so invariant_inv_curMin_spec gives the right disjunct with existential witnesses. We need to show nums[i]! is achieved as a suffix sum ending at i (use start = i, len = 1) and that it's minimal. The key condition is if_pos_2 : 0 < curMin and if_pos_3 : nums[i]! < minSum. Since curMin ≤ all suffix sums ending before i+1, and nums[i]! < minSum ≤ curMin, nums[i]! is less than all previous suffix sums. The single element nums[i]! at position i achieves the sum, and for minimality we need: for any start < i+1, the suffix sum from start to i is ≥ nums[i]!. For start = i, the sum is nums[i]!. For start < i, the suffix sum = (suffix sum from start to i-1) + nums[i]!. Since curMin > 0 (from if_pos_2), and curMin ≤ suffix sum from start to i-1 for any start < i, we get suffix sum ≥ curMin + nums[i]! > nums[i]! (since curMin > 0). So nums[i]! ≤ all suffix sums.
-/
theorem goal_24 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_pos_3 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    constructor;
    · use i; simp [if_pos];
    · intro start hstart;
      by_cases hstart_lt_i : start < i;
      · rw [ Nat.succ_sub hstart_lt_i.le ];
        rw [ Finset.sum_range_succ ];
        rw [ add_tsub_cancel_of_le hstart_lt_i.le ];
        exact le_add_of_nonneg_left ( by linarith [ invariant_inv_curMin_spec.resolve_left if_neg |>.2 start hstart_lt_i ] );
      · norm_num [ show start = i by linarith ]

/-
PROVIDED SOLUTION
We need to show curMax + nums[i]! is the new maxSum. From hypotheses: if_pos_1 says maxSum < curMax + nums[i]!, and invariant_inv_maxSum_spec (right disjunct since i ≠ 0) says maxSum is achieved by some subarray and bounds all subarrays within [0,i). We need to show curMax + nums[i]! is achieved by some subarray within [0,i+1) and bounds all subarrays. For achievability: since curMax is achieved by some suffix sum ending at i-1 (from invariant_inv_curMax_spec, right disjunct), say starting at s with range i-s, extending by 1 gives sum curMax + nums[i]! with range i-s+1 ending at i+1. For maximality: any subarray [start, start+len) with start+len ≤ i has sum ≤ maxSum < curMax + nums[i]!. For subarrays ending at i+1 (start+len = i+1), they are suffix sums from start to i = (suffix from start to i-1) + nums[i]! ≤ curMax + nums[i]! since suffix sums to i-1 are ≤ curMax. If start = i, the sum is nums[i]! = 0 + nums[i]! ≤ curMax + nums[i]! (since curMax ≥ 0 from if_neg_1).
-/
theorem goal_25 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_pos_3 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMax + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ curMax + nums[i]! := by
    refine' ⟨ _, _ ⟩;
    · -- Let's choose the start and length for the subarray that achieves the sum curMax + nums[i]!.
      obtain ⟨start, hstart₁, hstart₂⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax := by
        aesop;
      refine' ⟨ start, _, i - start + 1, _, _, _ ⟩ <;> norm_num at * <;> try omega;
      rw [ Finset.sum_range_succ, hstart₂ ];
      rw [ add_tsub_cancel_of_le hstart₁.le ];
    · intro start len hstart hlen hstart_len
      by_cases hstart_i : start < i;
      · by_cases hlen_i : start + len ≤ i;
        · grind +ring;
        · -- Since `start + len > i`, we have `len = i - start + 1`.
          have hlen_eq : len = i - start + 1 := by
            grind +ring;
          simp_all +decide [ Finset.sum_range_succ ];
      · norm_num [ show start = i by linarith ] at *;
        interval_cases len ; norm_num at * ; linarith!

theorem goal_26 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_pos_3 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    -- To prove the existence of such a start and x, we can take start = i and x = 1.
    use ⟨i, by linarith, 1, by linarith, by linarith, by simp⟩;
    intro start len hstart hlen hstart_len
    by_cases hstart_i : start < i;
    · by_cases hlen_i : len ≤ i - start;
      · grind;
      · have hlen_eq : len = i - start + 1 := by
          grind +ring;
        simp_all +decide [ Finset.sum_range_succ ];
        exact le_trans ( by positivity ) ( invariant_inv_curMin_spec.2 start hstart_i );
    · norm_num [ show start = i by linarith ] at *;
      interval_cases len ; norm_num

theorem goal_27 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_neg_2 : minSum ≤ nums[i]!) : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    exact?

theorem goal_28 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_neg_2 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    constructor;
    · obtain ⟨start, hstart⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax := by
        aesop;
      use start;
      rw [ ← hstart.2, show i + 1 - start = ( i - start ) + 1 by rw [ tsub_add_eq_add_tsub hstart.1.le ] ] ; simp +decide [ Finset.sum_range_succ ];
      exact ⟨ le_of_lt hstart.1, by rw [ add_tsub_cancel_of_le hstart.1.le ] ⟩;
    · intro start hstart
      by_cases hstart_lt_i : start < i;
      · simp_all +decide [ Nat.succ_sub ( le_of_lt hstart_lt_i ) ];
        simp_all +decide [ Finset.sum_range_succ ];
      · norm_num [ show start = i by linarith ] at * ; linarith

theorem goal_29 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_neg_2 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    -- For the first part, we can choose start = i.
    use ⟨i, by
      norm_num [ add_tsub_cancel_left ]⟩
    generalize_proofs at *;
    intro start hstart; rcases lt_trichotomy start i with ( h | rfl | h ) <;> norm_num at *;
    · rw [ Nat.sub_add_comm hstart ];
      simp +decide [ Finset.sum_range_succ ];
      rw [ Nat.add_sub_of_le hstart ];
      exact le_add_of_nonneg_left ( by linarith [ invariant_inv_curMin_spec.resolve_left if_neg |>.2 start h ] );
    · linarith

/-
PROVIDED SOLUTION
This is essentially identical to goal_25 but with different branching conditions (if_neg_2 : curMin ≤ 0 instead of if_pos_2 : 0 < curMin, and if_neg_2 : minSum ≤ nums[i]! instead of if_pos_3 : nums[i]! < minSum). The goal is the same as goal_25. Use the same approach: for achievability, extend the suffix achieving curMax by one element. For maximality, split into subarrays ending before i+1 (bounded by maxSum < curMax + nums[i]!) and subarrays ending at i+1 (suffix sum ≤ curMax + nums[i]! since suffix to i-1 ≤ curMax and for start=i, sum = nums[i]! ≤ curMax + nums[i]! since curMax ≥ 0).
-/
theorem goal_30 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_neg_2 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMax + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ curMax + nums[i]! := by
    apply And.intro;
    · rcases invariant_inv_curMax_spec with h|h <;> simp_all +decide;
      obtain ⟨ ⟨ start, hstart₁, hstart₂ ⟩, hstart₃ ⟩ := h;
      use start, by linarith, i - start + 1;
      simp_all +decide [ Finset.sum_range_succ ];
      exact ⟨ by norm_num; linarith [ Nat.sub_add_cancel hstart₁.le ], by rw [ add_tsub_cancel_of_le hstart₁.le ] ; exact? ⟩;
    · intro start len hstart hlen hstart_len
      by_cases hstart_i : start < i;
      · by_cases hlen_i : start + len ≤ i;
        · grind +ring;
        · -- Since `start + len > i`, we have `len = i - start + 1`.
          have hlen_eq : len = i - start + 1 := by
            norm_num at * ; omega;
          simp_all +decide [ Finset.sum_range_succ ];
      · norm_num [ show start = i by linarith ] at *;
        interval_cases len ; norm_num at * ; linarith!

theorem goal_31 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_pos_2 : OfNat.ofNat 0 < curMin) (if_neg_2 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    constructor;
    · rcases invariant_inv_minSum_spec with h|h <;> simp_all +decide;
      exact ⟨ h.1.choose, le_of_lt h.1.choose_spec.1, h.1.choose_spec.2.choose, h.1.choose_spec.2.choose_spec.1, by linarith [ h.1.choose_spec.1, h.1.choose_spec.2.choose_spec.2.1 ], h.1.choose_spec.2.choose_spec.2.2 ⟩;
    · intro start len hstart hlen hstart_len
      by_cases hstart_i : start < i;
      · by_cases hlen_i : len ≤ i - start;
        · exact invariant_inv_minSum_spec.resolve_left if_neg |>.2 start len hstart_i hlen ( by omega );
        · norm_num +zetaDelta at *;
          rw [ show len = i - start + 1 by omega ];
          rw [ Finset.sum_range_succ ];
          rw [ show start + ( i - start ) = i by rw [ add_tsub_cancel_of_le hstart ] ] ; linarith [ invariant_inv_minSum_spec.resolve_left if_neg |>.2 start ( i - start ) hstart_i ( Nat.sub_pos_of_lt hstart_i ) ( by omega ) ] ;
      · norm_num [ show start = i by linarith ] at *;
        interval_cases len ; aesop

theorem goal_32 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMin ≤ OfNat.ofNat 0) (if_neg_3 : minSum ≤ curMin + nums[i]!) : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    -- By definition of Finset.sum_range_succ, we can split the sum into the sum up to i and the element at i.
    simp [Finset.sum_range_succ]

theorem goal_33 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMin ≤ OfNat.ofNat 0) (if_neg_3 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    -- Since `invariant_inv_curMax_spec` is false, there must be some `start < i` where the sum of the range from `start` to `i - start` is equal to `curMax`.
    obtain ⟨start, hstart_lt, hsum⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax := by
      exact invariant_inv_curMax_spec.resolve_left if_neg |>.1;
    refine' ⟨ ⟨ start, _, _ ⟩, _ ⟩ <;> norm_num at *;
    · linarith;
    · rw [ ← hsum, Nat.sub_add_comm hstart_lt.le ];
      convert Finset.sum_range_succ _ _ using 2 ; simp +decide [ add_comm, hstart_lt.le ];
    · intro start hstart_le_i; rcases lt_or_eq_of_le hstart_le_i with hstart_lt | rfl <;> simp_all +decide [ Nat.sub_add_comm ] ;
      simp_all +decide [ Finset.sum_range_succ ]

theorem goal_34 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMin ≤ OfNat.ofNat 0) (if_neg_3 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    -- Since $i$ is not zero and $i < \text{nums.size}$, we can use the induction hypothesis on $i$.
    have h_ind : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin := by
      exact invariant_inv_curMin_spec.resolve_left if_neg |>.1
    generalize_proofs at *;
    -- By the induction hypothesis, there exists a start < i such that the sum of the range from start to i-1 is curMin.
    obtain ⟨start, hstart_lt, hstart_sum⟩ := h_ind;
    use ⟨start, by
      exact Nat.lt_succ_of_lt hstart_lt, by
      simp +decide [ ← hstart_sum, Nat.sub_add_comm hstart_lt.le, Finset.sum_range_succ ];
      rw [ add_tsub_cancel_of_le hstart_lt.le ]⟩;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    generalize_proofs at *;
    intro start hstart_lt; by_cases hstart_lt_i : start < i <;> simp_all +decide [ Nat.sub_add_comm, Finset.sum_range_succ ] ;
    cases hstart_lt_i.eq_or_lt <;> first | linarith | aesop;

theorem goal_35 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMin ≤ OfNat.ofNat 0) (if_neg_3 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMax + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ curMax + nums[i]! := by
    -- Since $curMin \leq 0$ and $minSum \leq curMin$, it follows that $minSum \leq 0$.
    have h_min_le_zero : minSum ≤ 0 := by
      exact le_trans invariant_inv_min_le_curMin if_neg_2;
    refine' ⟨ _, _ ⟩;
    · rcases invariant_inv_curMax_spec with ( rfl | ⟨ ⟨ start, hstart, hsum ⟩, hle ⟩ ) <;> norm_num at *;
      use start, by linarith, i - start + 1; simp_all +decide [ Finset.sum_range_succ ] ;
      exact ⟨ by linarith [ Nat.sub_add_cancel hstart.le ], by rw [ add_tsub_cancel_of_le hstart.le ] ; exact by exact? ⟩;
    · intro start len hstart hlen hstart_len
      by_cases hstart_i : start < i;
      · by_cases hlen_i : len ≤ i - start + 1 <;> simp_all +decide [ Finset.sum_range_add ];
        · by_cases hlen_eq : len = i - start + 1 <;> simp_all +decide [ Finset.sum_range_add ];
          exact le_trans ( invariant_inv_maxSum_spec.2 start len hstart_i hlen ( by omega ) ) ( by linarith );
        · grind +ring;
      · norm_num [ show start = i by linarith ] at *;
        interval_cases len ; norm_num ; linarith! [ show nums[i]! ≤ curMax + nums[i]! from by linarith! ] ;

theorem goal_36 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (if_pos_1 : maxSum < curMax + nums[i]!) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMin ≤ OfNat.ofNat 0) (if_neg_3 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    -- By definition of `minSum`, we know that there exists some `start` and `x` such that the sum of the range `x` starting at `start` is equal to `minSum`.
    obtain ⟨start, x, hx₁, hx₂, hx₃⟩ : ∃ start < i, ∃ x, 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum := by
      exact invariant_inv_minSum_spec.resolve_left if_neg |>.1;
    refine' ⟨ ⟨ start, by linarith, hx₁, hx₂, by linarith, hx₃.2 ⟩, _ ⟩;
    intro start len h₁ h₂ h₃; cases lt_or_eq_of_le ( Nat.le_of_lt_succ h₁ ) <;> simp_all +decide ;
    · by_cases h₄ : start + len ≤ i;
      · exact invariant_inv_minSum_spec.2 _ _ ‹_› ‹_› ‹_›;
      · -- Since $start + len > i$, we have $len = i - start + 1$.
        have h_len : len = i - start + 1 := by
          norm_num at * ; omega;
        simp_all +decide [ Finset.sum_range_succ ];
        exact le_trans invariant_inv_min_le_curMin ( by linarith [ invariant_inv_curMin_spec.2 start ( by linarith ) ] );
    · interval_cases len ; simp_all +decide [ Finset.sum_range_succ ] ; linarith [ invariant_inv_min_le_curMin, invariant_inv_minSum_spec.2 _ _ x hx₂ ( by linarith ) ] ;

theorem goal_37 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_pos_2 : nums[i]! < minSum) : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    -- By definition of Finset.sum_range_succ, we can split the sum into the sum up to i and the term at i.
    simp [Finset.sum_range_succ]

theorem goal_38 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_pos_2 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    constructor;
    · obtain ⟨start, hstart⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax := by
        aesop;
      use start, by
        exact Nat.lt_succ_of_lt hstart.1
      generalize_proofs at *;
      rw [ ← hstart.2, Nat.sub_add_comm hstart.1.le ] ; simp +decide [ Finset.sum_range_succ ] ; ring;
      rw [ add_tsub_cancel_of_le hstart.1.le ];
    · -- By splitting into cases based on whether start is less than i or equal to i, we can apply the induction hypothesis and the properties of curMax and nums[i]!.
      intros start hstart
      by_cases hstart_lt_i : start < i;
      · convert add_le_add ( invariant_inv_curMax_spec.resolve_left ( by aesop ) |>.2 start hstart_lt_i ) le_rfl using 1;
        simp +arith +decide [ Nat.sub_add_comm hstart_lt_i.le, Finset.sum_range_succ ];
        rw [ add_tsub_cancel_of_le hstart_lt_i.le ];
      · norm_num [ show start = i by linarith ] at * ; linarith!;

theorem goal_39 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_pos_2 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    apply And.intro;
    · use i; simp [if_pos];
    · intro start hstart
      by_cases hstart_lt_i : start < i
      generalize_proofs at *;
      · rw [ show i + 1 - start = ( i - start ) + 1 by omega, Finset.sum_range_succ ];
        rw [ add_tsub_cancel_of_le hstart_lt_i.le ] ; linarith [ show ∑ k ∈ Finset.range ( i - start ), nums[start + k]! ≥ 0 from by exact le_trans ( by linarith ) ( invariant_inv_curMin_spec.resolve_left ( by aesop ) |>.2 start hstart_lt_i ) ] ;
      · norm_num [ show start = i by linarith ] at *

theorem goal_40 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_pos_2 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    constructor;
    · rcases invariant_inv_maxSum_spec with ( rfl | ⟨ ⟨ start, hstart₁, x, hx₁, hx₂, hx₃ ⟩, hx₄ ⟩ ) <;> norm_num at *;
      exact ⟨ start, by linarith, x, hx₁, by linarith, hx₃ ⟩;
    · intro start len hstart hlen hstart_len
      by_cases hstart_lt_i : start < i;
      · cases hstart_len.eq_or_lt <;> simp_all +decide [ Nat.lt_succ_iff ];
        simp_all +decide [ show len = i - start + 1 by linarith [ Nat.sub_add_cancel hstart ] ];
        simp_all +decide [ Finset.sum_range_succ ];
        linarith [ invariant_inv_curMax_spec.2 start hstart_lt_i ];
      · norm_num [ show start = i by linarith ] at *;
        norm_num [ show len = 1 by linarith ] at * ; linarith

theorem goal_41 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_pos_2 : nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    constructor;
    · exact ⟨ i, Nat.lt_succ_self _, 1, by norm_num, by norm_num, by norm_num ⟩;
    · intros start len hstart hlen hlen_le_i_plus_1
      by_cases hstart_le_i : start ≤ i;
      · by_cases hlen_le_i : len ≤ i - start + 1;
        · rcases hstart_le_i.eq_or_lt with rfl | hstart_lt_i <;> rcases hlen_le_i.eq_or_lt with hlen_eq | hlen_lt <;> simp_all +decide [ Nat.succ_eq_add_one ];
          · simp +decide [ Finset.sum_range_succ, hstart_lt_i.le ];
            grind +ring;
          · linarith [ invariant_inv_minSum_spec.2 start len hstart_lt_i hlen ( by linarith [ Nat.sub_add_cancel hstart_le_i ] ) ];
        · grind +ring;
      · grind +ring

theorem goal_42 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_neg_3 : minSum ≤ nums[i]!) : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    -- The sum over `Finset.range (i + 1)` is the same as the sum over `Finset.range i` plus the element at `i`.
    simp [Finset.sum_range_succ]

theorem goal_43 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_neg_3 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    obtain ⟨start, hstart⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax := by
      aesop;
    constructor;
    · use start; simp [hstart];
      rw [ ← hstart.2, show i + 1 - start = ( i - start ) + 1 by rw [ tsub_add_eq_add_tsub hstart.1.le ] ] ; simp +decide [ Finset.sum_range_succ ] ; ring;
      exact ⟨ hstart.1.le, by rw [ add_tsub_cancel_of_le hstart.1.le ] ⟩;
    · intro start hstart
      by_cases hstart_lt_i : start < i;
      · simp_all +decide [ Nat.succ_sub ( show start ≤ i from Nat.le_of_lt hstart_lt_i ), Finset.sum_range_succ ];
      · norm_num [ show start = i by linarith ] at * ; aesop ( simp_config := { singlePass := true } ) ;

theorem goal_44 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_neg_3 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    constructor;
    · use i; simp [if_pos];
    · intro start hstart;
      rcases invariant_inv_curMin_spec with h|h <;> simp_all +decide [ Finset.sum_range_succ ];
      cases hstart.eq_or_lt <;> simp_all +decide [ Nat.succ_sub ];
      simp_all +decide [ Finset.sum_range_succ ];
      exact le_trans if_pos_1.le ( h.2 _ ‹_› )

theorem goal_45 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_neg_3 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    -- By the induction hypothesis, there exists a start and x such that the sum of the range x equals maxSum. We can extend this by adding the current element nums[i]! to the subarray.
    obtain ⟨start, hstart, x, hx, hsum⟩ : ∃ start < i, ∃ x, 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum := by
      exact invariant_inv_maxSum_spec.resolve_left if_neg |>.1;
    refine' ⟨ ⟨ start, by linarith, x, hx, by linarith, hsum.2 ⟩, _ ⟩;
    intros start len hstart hlen hsum
    by_cases hstart_eq_i : start = i;
    · rcases len with ( _ | _ | len ) <;> simp_all +decide [ Finset.sum_range_succ' ];
      linarith [ invariant_inv_curMax_spec.2 _ hstart ];
    · by_cases hlen_eq_i : len ≤ i - start;
      · exact invariant_inv_maxSum_spec.resolve_left ( by aesop ) |>.2 start len ( by omega ) hlen ( by omega );
      · norm_num +zetaDelta at *;
        cases hstart.eq_or_lt <;> simp_all +decide [ Nat.sub_add_comm ];
        rw [ show len = i - start + 1 by linarith [ Nat.sub_add_cancel hstart ] ] ; simp +decide [ *, Finset.sum_range_succ ] ; linarith [ invariant_inv_curMax_spec.2 start ‹_›, invariant_inv_curMin_spec.2 start ‹_› ] ;

theorem goal_46 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_pos_1 : OfNat.ofNat 0 < curMin) (if_neg_3 : minSum ≤ nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    rcases invariant_inv_minSum_spec with ( rfl | ⟨ ⟨ start, hstart₁, x, hx₁, hx₂, hx₃ ⟩, hx₄ ⟩ ) <;> norm_num at *;
    refine' ⟨ ⟨ start, by linarith, x, hx₁, by linarith, hx₃ ⟩, _ ⟩;
    intros start len hstart hlen hlen_le_i_plus_1
    by_cases hstart_eq_i : start = i;
    · rcases len with ( _ | _ | len ) <;> simp_all +decide [ Finset.sum_range_succ' ];
    · by_cases hstart_lt_i : start < i;
      · by_cases hlen_le_i : start + len ≤ i;
        · exact hx₄ start len hstart_lt_i hlen hlen_le_i;
        · norm_num [ show len = i - start + 1 by omega ] at *;
          simp_all +decide [ Finset.sum_range_succ ];
          linarith [ invariant_inv_curMin_spec.2 start hstart_lt_i ];
      · exact False.elim <| hstart_lt_i <| lt_of_le_of_ne hstart hstart_eq_i

theorem goal_47 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_pos_1 : curMin + nums[i]! < minSum) : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    -- The sum up to i+1 is the sum up to i plus the element at i.
    simp [Finset.sum_range_succ]

theorem goal_48 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_pos_1 : curMin + nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    -- By definition of `curMax`, we know that `curMax` is the maximum sum of any subarray ending at index `i`.
    obtain ⟨start, hstart_lt_i, hsum_eq_curMax⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax := by
      aesop;
    refine' ⟨ ⟨ start, by linarith, _ ⟩, _ ⟩;
    · rw [ ← hsum_eq_curMax, show i + 1 - start = ( i - start ) + 1 by omega, Finset.sum_range_succ ];
      rw [ add_tsub_cancel_of_le hstart_lt_i.le ];
    · intro start hstart_lt_i_plus_1; by_cases hstart_lt_i : start < i <;> simp_all +decide [ Nat.sub_add_comm ] ;
      · simp_all +decide [ Finset.sum_range_succ ];
      · cases hstart_lt_i.eq_or_lt <;> first | linarith | aesop;

theorem goal_49 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_pos_1 : curMin + nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    -- By definition of `invariant_inv_curMin_spec`, we know that there exists a start < i such that the sum of the range up to i minus start is equal to curMin.
    obtain ⟨start, hstart_lt_i, hsum_eq_curMin⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin := by
      exact invariant_inv_curMin_spec.resolve_left if_neg |>.1;
    refine' ⟨ ⟨ start, _, _ ⟩, _ ⟩ <;> simp_all +decide [ Finset.sum_range_succ ];
    · linarith;
    · rw [ ← hsum_eq_curMin, Nat.sub_add_comm hstart_lt_i.le ] ; simp +decide [ Finset.sum_range_succ ] ; ring;
      rw [ add_tsub_cancel_of_le hstart_lt_i.le ] ; exact?;
    · intro start hstart_le_i; rcases lt_or_eq_of_le hstart_le_i with hstart_lt_i | rfl <;> simp_all +decide [ Finset.sum_range_succ, Nat.sub_add_comm ] ;

theorem goal_50 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_pos_1 : curMin + nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    -- Let's consider the two cases from `invariant_inv_maxSum_spec`.
    cases' invariant_inv_maxSum_spec with h h;
    · contradiction;
    · -- Since the maximum sum up to i is already the maximum, adding the next element can't exceed that maximum. Therefore, the maximum sum up to i+1 is the same as the maximum sum up to i, which is ≤ maxSum.
      have h_max_le : ∀ start len, start < i + 1 → 1 ≤ len → start + len ≤ i + 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
        intros start len hstart hlen hsum
        by_cases hstart_eq_i : start = i;
        · rcases len with ( _ | _ | len ) <;> simp_all +decide [ Finset.sum_range_succ' ];
          linarith [ show 0 ≤ curMax from by assumption ];
        · by_cases hstart_lt_i : start < i;
          · by_cases hlen_eq_i : len = i - start + 1;
            · simp_all +decide [ Finset.sum_range_succ ];
              linarith [ invariant_inv_curMax_spec.2 start hstart_lt_i ];
            · exact h.2 start len hstart_lt_i hlen ( by norm_num at *; omega );
          · omega;
      exact ⟨ by obtain ⟨ start, hstart, x, hx, hx', hx'' ⟩ := h.1; exact ⟨ start, by linarith, x, hx, by linarith, hx'' ⟩, h_max_le ⟩

theorem goal_51 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_pos_1 : curMin + nums[i]! < minSum) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMin + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → curMin + nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    constructor
    all_goals generalize_proofs at *;
    · -- Let's choose `start` as the start from `invariant_inv_curMin_spec` and `len` as `i - start + 1`.
      obtain ⟨start, hstart, hsum⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin := by
        exact invariant_inv_curMin_spec.resolve_left if_neg |>.1 |> fun ⟨ start, hstart, hsum ⟩ => ⟨ start, hstart, hsum ⟩ ;
      generalize_proofs at *;
      use start, by
        grind, i - start + 1, by
        exact Nat.le_add_left _ _, by
        simp +arith +decide [ hstart.le ]
      generalize_proofs at *; (
      rw [ ← hsum, Finset.sum_range_succ ] ; simp +decide [ Nat.sub_add_cancel hstart.le ] ; ring!;
      rw [ add_tsub_cancel_of_le hstart.le ]) -- (continuation of proof, see next goal);
    · intros start len hstart hlen hstart_len
      by_cases hstart_lt_i : start < i;
      · by_cases hlen_le_i_minus_start : len ≤ i - start + 1 <;> simp_all +decide [ Finset.sum_range_add ] ; (
        by_cases hlen_eq_i_minus_start_plus_1 : len = i - start + 1 <;> simp_all +decide [ Finset.sum_range_succ ] ; (
        exact le_trans ( by linarith ) ( invariant_inv_minSum_spec.2 start len hstart_lt_i hlen ( by omega ) ) |> le_trans <| by aesop;));
        (generalize_proofs at *; (
        grind););
      · norm_num [ show start = i by linarith ] at *;
        interval_cases len ; norm_num at * ; linarith! [ show nums[i]! = nums[i]! from rfl ] ;

theorem goal_52 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_neg_4 : minSum ≤ curMin + nums[i]!) : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    -- Apply the lemma that states the sum up to i+1 is the sum up to i plus the element at i.
    rw [Finset.sum_range_succ]

theorem goal_53 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_neg_4 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    constructor;
    · obtain ⟨ start, hstart₁, hstart₂ ⟩ := invariant_inv_curMax_spec.resolve_left if_neg |> And.left;
      use start;
      rw [ ← hstart₂, Nat.sub_add_comm hstart₁.le ];
      simp +decide [ Finset.sum_range_succ, hstart₁.le ];
    · intro start hstart; cases lt_or_eq_of_le ( Nat.le_of_lt_succ hstart ) <;> simp_all +decide [ Finset.sum_range_succ ] ;
      convert add_le_add ( invariant_inv_curMax_spec.2 start ‹_› ) le_rfl using 1;
      rw [ Nat.sub_add_comm hstart ];
      convert Finset.sum_range_succ _ _ using 2 ; aesop

theorem goal_54 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_neg_4 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    -- Apply the hypothesis `h_sum` to each start in the range.
    apply And.intro
    generalize_proofs at *;
    · obtain ⟨start, hstart⟩ : ∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin := by
        exact invariant_inv_curMin_spec.resolve_left if_neg |>.1;
      use start;
      rw [ ← hstart.2, show i + 1 - start = ( i - start ) + 1 by rw [ tsub_add_eq_add_tsub hstart.1.le ] ] ; simp +decide [ Finset.sum_range_succ ];
      exact ⟨ le_of_lt hstart.1, by rw [ add_tsub_cancel_of_le hstart.1.le ] ⟩;
    · intro start hstart; cases lt_or_eq_of_le ( Nat.le_of_lt_succ hstart ) <;> simp_all +decide [ Finset.sum_range_succ ] ;
      rw [ show i + 1 - start = ( i - start ) + 1 by omega, Finset.sum_range_succ ];
      simp_all +decide [ add_tsub_cancel_of_le ( show start ≤ i from hstart ) ]

theorem goal_55 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_neg_4 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    rcases invariant_inv_maxSum_spec with h|h <;> simp_all +decide [ Nat.lt_succ_iff ];
    refine' ⟨ _, _ ⟩;
    · rcases h.1 with ⟨ start, hstart, x, hx, hx', hx'' ⟩ ; exact ⟨ start, by linarith, x, hx, by linarith, hx'' ⟩ ;
    · intro start len hstart hlen hlen'; rcases eq_or_lt_of_le hstart with rfl | hstart' <;> simp_all +decide [ Nat.lt_succ_iff ] ;
      · rcases len with ( _ | _ | len ) <;> norm_num at *;
        grind +ring;
      · by_cases hlen'' : start + len ≤ i;
        · exact h.2 start len hstart' hlen hlen'';
        · -- Since $start + len > i$, we have $len = i - start + 1$.
          have hlen_eq : len = i - start + 1 := by
            grind;
          simp_all +decide [ Finset.sum_range_succ ];
          linarith [ invariant_inv_curMax_spec.2 start hstart' ]

theorem goal_56 (nums : Array ℤ) (curMax : ℤ) (curMin : ℤ) (i : ℕ) (maxSum : ℤ) (minSum : ℤ) (invariant_inv_i_le_n : i ≤ nums.size) (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax) (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_min_le_curMin : minSum ≤ curMin) (if_pos : i < nums.size) (if_neg : ¬i = OfNat.ofNat 0) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_max_ge_curMax : curMax ≤ maxSum) (if_neg_1 : OfNat.ofNat 0 ≤ curMax) (if_neg_2 : curMax + nums[i]! ≤ maxSum) (if_neg_3 : curMin ≤ OfNat.ofNat 0) (if_neg_4 : minSum ≤ curMin + nums[i]!) : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    apply And.intro;
    · rcases invariant_inv_minSum_spec with h|h <;> simp_all +decide;
      obtain ⟨ ⟨ start, hstart, x, hx₁, hx₂, hx₃ ⟩, hx₄ ⟩ := h; exact ⟨ start, by linarith, x, hx₁, by linarith, hx₃ ⟩ ;
    · intro start len hstart hlen hstart_len
      by_cases hstart_i : start < i;
      · by_cases hlen_i : len ≤ i - start <;> simp_all +decide [ Finset.sum_range_add ];
        · exact invariant_inv_minSum_spec.2 start len hstart_i hlen ( by omega ) |> le_trans <| by aesop;
        · rw [ show len = i - start + 1 by linarith [ Nat.sub_add_cancel hstart ] ] ; simp_all +decide [ Finset.sum_range_add ] ;
          grind;
      · norm_num [ show start = i by linarith ] at *;
        interval_cases len ; norm_num at * ; linarith

/-
PROBLEM
Helper: for non-wrapping segment, circSegmentSum equals linear sum

PROVIDED SOLUTION
Unfold circSegmentSum. Each index (start + k) % arr.size = start + k because start + k < arr.size (since k < len and start + len ≤ arr.size). Use Finset.sum_congr to rewrite each term.
-/
lemma circSegmentSum_non_wrap (arr : Array Int) (start len : Nat)
    (h_sz : arr.size > 0) (h_start : start < arr.size) (h_len : start + len ≤ arr.size) :
    circSegmentSum arr start len = ∑ k ∈ Finset.range len, arr[start + k]! := by
  -- Since `start + k < arr.size` for all `k` in the range `0` to `len - 1`, the modulo operation can be removed.
  have h_mod : ∀ k ∈ Finset.range len, (start + k) % arr.size = start + k := by
    exact fun k hk => Nat.mod_eq_of_lt <| by linarith [ Finset.mem_range.mp hk ] ;
  convert Finset.sum_congr rfl fun k hk => congr_arg ( fun x => arr[x]! ) ( h_mod k hk ) using 1

/-
PROBLEM
Helper: for wrapping segment, circSegmentSum = total - complement

PROVIDED SOLUTION
We need to show that for a wrapping segment (arr.size < start + len), circSegmentSum arr start len equals total - complement_sum.

Unfold circSegmentSum. Split Finset.range len into Finset.range (arr.size - start) ∪ Finset.Ico (arr.size - start) len using Finset.sum_range_add_sum_Ico.

For the first part (k < arr.size - start): (start + k) % arr.size = start + k since start + k < arr.size.

For the second part (arr.size - start ≤ k < len): (start + k) % arr.size = start + k - arr.size since arr.size ≤ start + k < start + len = arr.size + (start + len - arr.size), so start + k - arr.size < start + len - arr.size.

Now the full sum = ∑ k in range(arr.size - start), arr[start + k]! + ∑ k in range(len - (arr.size - start)), arr[k]!

The total = ∑ j in range(arr.size), arr[j]! can be split as:
∑ j in range(start + len - arr.size), arr[j]! + ∑ j in Ico(start+len-arr.size, start), arr[j]! + ∑ j in Ico(start, arr.size), arr[j]!

The segment sum = ∑ j in Ico(start, arr.size), arr[j]! + ∑ j in range(start+len-arr.size), arr[j]!

So segment = total - ∑ j in Ico(start+len-arr.size, start), arr[j]!

The complement: start at (start+len) % arr.size = start+len-arr.size, length arr.size - len. The complement indices go from start+len-arr.size to start+len-arr.size + (arr.size - len) - 1 = start - 1. So the complement sum = ∑ k in range(arr.size-len), arr[(start+len-arr.size) + k]! = ∑ j in Ico(start+len-arr.size, start), arr[j]!. And ((start+len) % arr.size + k) % arr.size = (start+len-arr.size+k) % arr.size = start+len-arr.size+k since this is < start < arr.size.
-/
lemma circSegmentSum_wrap (arr : Array Int) (start len : Nat)
    (h_sz : arr.size > 0) (h_start : start < arr.size) (h_len1 : 1 ≤ len) (h_len2 : len ≤ arr.size)
    (h_wrap : arr.size < start + len) :
    circSegmentSum arr start len =
      ∑ j ∈ Finset.range arr.size, arr[j]! -
      ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! := by
  -- By definition of circSegmentSum, we can split the sum into two parts: one from start to the end of the array and one from the beginning of the array to the end of the segment.
  have h_split : circSegmentSum arr start len = ∑ k ∈ Finset.range (arr.size - start), arr[start + k]! + ∑ k ∈ Finset.range (len - (arr.size - start)), arr[k]! := by
    unfold circSegmentSum;
    rw [ ← Finset.sum_range_add_sum_Ico _ ( show arr.size - start ≤ len from by omega ) ];
    rw [ Finset.sum_Ico_eq_sum_range ];
    congr! 2;
    · rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp ‹_›, Nat.sub_add_cancel h_start.le ] ) ];
    · simp +decide [ ← add_assoc, Nat.mod_eq_of_lt ( show ‹_› < arr.size from by linarith [ Finset.mem_range.mp ‹_›, Nat.sub_add_cancel ( show arr.size - start ≤ len from by omega ) ] ) ];
      simp +decide [ add_tsub_cancel_of_le h_start.le, Nat.mod_eq_of_lt ( show ‹_› < arr.size from by linarith [ Finset.mem_range.mp ‹_›, Nat.sub_add_cancel ( show arr.size - start ≤ len from by omega ) ] ) ];
  -- By definition of complement, we can split the sum into two parts: one from start to the end of the array and one from the beginning of the array to the end of the segment.
  have h_complement : ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! = ∑ k ∈ Finset.range (arr.size - len), arr[(start + len - arr.size + k) % arr.size]! := by
    simp +decide [ Nat.mod_eq_sub_mod ( show arr.size ≤ start + len from h_wrap.le ) ];
  -- By definition of complement, we can split the sum into two parts: one from start to the end of the array and one from the beginning of the array to the end of the segment. The complement sum is the sum from start+len-arr.size to start.
  have h_complement_split : ∑ k ∈ Finset.range (arr.size - len), arr[(start + len - arr.size + k) % arr.size]! = ∑ j ∈ Finset.Ico (start + len - arr.size) start, arr[j]! := by
    rw [ Finset.sum_Ico_eq_sum_range ];
    rw [ show start - ( start + len - arr.size ) = arr.size - len by omega ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp hx, Nat.sub_add_cancel h_len2, Nat.sub_add_cancel h_wrap.le ] ) ] ;
  -- The total sum is the sum from 0 to arr.size-1.
  have h_total : ∑ j ∈ Finset.range arr.size, arr[j]! = ∑ j ∈ Finset.range (start + len - arr.size), arr[j]! + ∑ j ∈ Finset.Ico (start + len - arr.size) start, arr[j]! + ∑ j ∈ Finset.Ico start arr.size, arr[j]! := by
    rw [ Finset.sum_range_add_sum_Ico, Finset.sum_range_add_sum_Ico ] <;> omega;
  simp_all +decide [ Finset.sum_Ico_eq_sum_range ];
  grind

/-
PROBLEM
Helper: for wrapping segment complement, the complement sum is a linear sum

PROVIDED SOLUTION
Since start + len wraps, (start+len) % arr.size = start + len - arr.size < start < arr.size. Then (start+len) % arr.size + k < arr.size for k < arr.size - len (because (start+len)%n + (n-len) = start+len-n+n-len = start ≤ n-1 < n). So ((start+len)%n + k) % n = (start+len)%n + k. Apply Finset.sum_congr.
-/
lemma circSegmentSum_wrap_complement (arr : Array Int) (start len : Nat)
    (h_sz : arr.size > 0) (h_start : start < arr.size) (h_len1 : 1 ≤ len) (h_len2 : len ≤ arr.size)
    (h_wrap : arr.size < start + len) (h_len3 : len < arr.size) :
    ∑ k ∈ Finset.range (arr.size - len), arr[((start + len) % arr.size + k) % arr.size]! =
    ∑ k ∈ Finset.range (arr.size - len), arr[(start + len) % arr.size + k]! := by
  -- Since $(start + len) \% arr.size + k < arr.size$ for all $k \in \{0, 1, ..., arr.size - len - 1\}$, the modulo operation does not change the value.
  have h_mod_eq : ∀ k ∈ Finset.range (arr.size - len), ((start + len) % arr.size + k) % arr.size = (start + len) % arr.size + k := by
    intro k hk
    have h_lt : (start + len) % arr.size + k < arr.size := by
      have h_lt : (start + len) % arr.size = start + len - arr.size := by
        rw [ Nat.mod_eq_sub_mod h_wrap.le, Nat.mod_eq_of_lt ] ; omega;
      generalize_proofs at *; (
      grind +ring)
    generalize_proofs at *; (
    exact Nat.mod_eq_of_lt h_lt)
  generalize_proofs at *; (
  exact Finset.sum_congr rfl fun x hx => by rw [ h_mod_eq x hx ] ;)

/-
PROVIDED SOLUTION
maxSum = i_4 < 0 means all elements are negative. postcondition requires achievability and maximality. Since i_3 = nums.size (from done_1 and invariant_inv_i_le_n), invariant_inv_maxSum_spec gives the right disjunct (i_3 ≠ 0 since nums.size > 0). For achievability: take the subarray from the invariant, it's valid since start < nums.size and 1 ≤ x and start + x ≤ nums.size, use circSegmentSum_non_wrap to convert. For maximality: for any valid circular segment, if it doesn't wrap (start + len ≤ nums.size), use circSegmentSum_non_wrap and invariant_inv_maxSum_spec.2. If it wraps, the sum = total - complement_sum. Since all subarrays have sum ≤ i_4 < 0, the total = sum of n elements = sum of each singleton ≤ n * i_4 and complement_sum is the sum of a contiguous subarray ≥ minSum. But total = total_1, and total - complement ≤ i_4 because complement ≥ minSum and total - minSum = total_1 - i_5, but we know i_4 < 0 ≤ i_4 is false... Actually since i_4 < 0, every single element has value ≤ i_4 < 0. If len = nums.size (full array), the sum = total_1 which is a contiguous sum of length nums.size, so total_1 ≤ i_4. For wrapping with len < n, the complement is a contiguous subarray of length n-len ≥ 1. complement_sum ≥ minSum. The wrapping sum = total_1 - complement_sum. We need total_1 - complement_sum ≤ i_4. Since total_1 ≤ i_4 (it's the sum of all elements, which is a contiguous subarray of length n) and complement_sum ≥ minSum, and i_4 < 0 so complement_sum ≤ i_4 < 0, we get total_1 - complement_sum ≤ i_4 - complement_sum ≤ i_4 - minSum... Hmm, we need complement_sum ≥ 0 but that's not guaranteed. Actually: total_1 - complement_sum ≤ i_4 iff total_1 - i_4 ≤ complement_sum. And total_1 is the full sum, and we can write total_1 = wrapping_part + complement_sum, so wrapping_part = total_1 - complement_sum. The wrapping subarray consists of elements from start to end and 0 to start+len-n-1, which has two contiguous pieces. Each piece has sum ≤ i_4, so the total wrapping sum ≤ 2*i_4 < i_4 since i_4 < 0. Wait no, that's wrong - the two pieces together might not each be a valid subarray. Actually, thinking more carefully: if the subarray wraps, it consists of indices start, start+1, ..., n-1, 0, 1, ..., start+len-n-1. The total sum is (sum from start to n-1) + (sum from 0 to start+len-n-1). The first part is a suffix sum ≤ i_1 (curMax suffix) ≤ i_4. The second part is a contiguous subarray sum from 0 to start+len-n-1 ≤ i_4. So the wrapping sum ≤ i_4 + i_4 = 2*i_4 < i_4 since i_4 < 0. Wait that works! Use circSegmentSum_non_wrap... Actually let me think again. For wrapping sums use circSegmentSum_wrap and show both pieces of the wrapping sum are ≤ i_4. But I think we can simplify: use the helper lemmas `circSegmentSum_non_wrap` and for wrapping case split the range into two parts each of which is a contiguous subarray with sum ≤ i_4.
-/
theorem goal_57 (nums : Array ℤ) (minSum : ℤ) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (i_4 : ℤ) (i_5 : ℤ) (total_1 : ℤ) (if_pos : i_4 < OfNat.ofNat 0) (invariant_inv_min_le_curMin : minSum ≤ i_2) (invariant_inv_i_le_n : i_3 ≤ nums.size) (invariant_inv_minSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_curMax_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_1) ∧ ∀ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! ≤ i_1) (invariant_inv_curMin_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_2) ∧ ∀ start < i_3, i_2 ≤ ∑ k ∈ Finset.range (i_3 - start), nums[start + k]!) (invariant_inv_maxSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = i_4) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4) (require_1 : OfNat.ofNat 0 < nums.size) (done_1 : nums.size ≤ i_3) (invariant_inv_max_ge_curMax : i_1 ≤ i_4) (snd_eq : minSum = i_5 ∧ ∑ j ∈ Finset.range i_3, nums[j]! = total_1) : postcondition nums i_4 := by
    -- Apply the helper lemma to show that all elements are ≤ i_4.
    have h_all_le_i4 : ∀ j < nums.size, nums[j]! ≤ i_4 := by
      have h_all_le_i4 : ∀ start len, start < i_3 → 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4 := by
        cases invariant_inv_maxSum_spec <;> aesop ( simp_config := { singlePass := true } ) ;
      exact fun j hj => by simpa using h_all_le_i4 j 1 ( by linarith ) ( by norm_num ) ( by linarith ) ;
    constructor;
    · obtain ⟨start, len, h_valid, h_sum⟩ : ∃ start len, isValidCircSegment nums start len ∧ circSegmentSum nums start len = i_4 := by
        have h_exists : ∃ start len, start < nums.size ∧ 1 ≤ len ∧ start + len ≤ nums.size ∧ circSegmentSum nums start len = i_4 := by
          obtain ⟨start, len, h_valid, h_sum⟩ : ∃ start len, start < i_3 ∧ 1 ≤ len ∧ start + len ≤ i_3 ∧ ∑ k ∈ Finset.range len, nums[start + k]! = i_4 := by
            cases invariant_inv_maxSum_spec <;> aesop;
          use start, len;
          exact ⟨ by linarith, h_sum.1, by linarith, by rw [ circSegmentSum_non_wrap nums start len ( by linarith ) ( by linarith ) ( by linarith ) ] ; exact h_sum.2.2 ⟩
        exact ⟨ h_exists.choose, h_exists.choose_spec.choose, ⟨ by linarith, h_exists.choose_spec.choose_spec.1, h_exists.choose_spec.choose_spec.2.1, by linarith [ h_exists.choose_spec.choose_spec.2.2.1 ] ⟩, h_exists.choose_spec.choose_spec.2.2.2 ⟩;
      use start, len;
    · intros start len h_valid
      have h_sum_le_i4 : circSegmentSum nums start len ≤ i_4 * len := by
        exact le_trans ( Finset.sum_le_sum fun _ _ => h_all_le_i4 _ <| Nat.mod_lt _ <| by linarith [ h_valid.1 ] ) <| by simp +decide [ mul_comm ] ;
      exact h_sum_le_i4.trans ( by exact le_trans ( mul_le_mul_of_nonpos_left ( Nat.cast_le.mpr h_valid.2.2.1 ) ( by linarith ) ) ( by norm_num ) )

/-
PROVIDED SOLUTION
postcondition nums (total_1 - i_5) where total_1 is the total array sum, i_5 = minSum, i_4 = maxSum ≥ 0, and maxSum < total - minSum. Since i_3 = nums.size (done_1 + i_le_n), all specs hold for the full array.

ACHIEVABILITY: From invariant_inv_minSum_spec, get start_min, len_min with sum = minSum = i_5. The complement circular subarray has start = (start_min + len_min) % n, len = n - len_min. If len_min < n, this is a valid circular segment. Its sum via circSegmentSum = total - minSum = total_1 - i_5. If len_min = n (minSum = total), then total_1 - i_5 = 0 but maxSum ≥ 0, and maxSum < total - minSum = 0, contradiction. So len_min < n.

For the complement: use circSegmentSum_non_wrap if it doesn't wrap, otherwise circSegmentSum_wrap. Actually the complement starting at (start_min + len_min) % n with length n - len_min: since start_min + len_min ≤ n, the complement start is (start_min + len_min) % n = start_min + len_min if < n, or 0 if = n. If start_min + len_min < n: complement goes from start_min + len_min to start_min + len_min + (n - len_min) - 1 = start_min + n - 1. If start_min = 0, this wraps. The key identity: circSegmentSum of complement = total - minSubarraySum.

MAXIMALITY: For any valid circular segment (s, l): if it doesn't wrap (s + l ≤ n), its sum ≤ maxSum = i_4 < total_1 - i_5. If it wraps, its sum = total - (complement sum). The complement is a contiguous subarray of length n - l, starting at (s + l) % n. complement sum ≥ minSum = i_5. So circular sum = total - complement ≤ total - minSum = total_1 - i_5. If l = n, circular sum = total = total_1. total_1 - i_5 ≥ total_1 iff i_5 ≤ 0. Since i_4 ≥ 0 and i_4 < total_1 - i_5, i_5 < total_1 - i_4 ≤ total_1. And since maxSum ≥ 0, there exists a non-negative element, so minSum ≤ 0 (single element minimization). Thus i_5 ≤ 0, and total_1 - i_5 ≥ total_1.
-/
theorem goal_58 (nums : Array ℤ) (minSum : ℤ) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (i_4 : ℤ) (i_5 : ℤ) (total_1 : ℤ) (invariant_inv_min_le_curMin : minSum ≤ i_2) (invariant_inv_i_le_n : i_3 ≤ nums.size) (invariant_inv_minSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_curMax_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_1) ∧ ∀ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! ≤ i_1) (invariant_inv_curMin_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_2) ∧ ∀ start < i_3, i_2 ≤ ∑ k ∈ Finset.range (i_3 - start), nums[start + k]!) (invariant_inv_maxSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = i_4) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4) (require_1 : OfNat.ofNat 0 < nums.size) (if_neg : OfNat.ofNat 0 ≤ i_4) (if_pos : i_4 < total_1 - i_5) (done_1 : nums.size ≤ i_3) (invariant_inv_max_ge_curMax : i_1 ≤ i_4) (snd_eq : minSum = i_5 ∧ ∑ j ∈ Finset.range i_3, nums[j]! = total_1) : postcondition nums (total_1 - i_5) := by
    constructor;
    · rcases invariant_inv_minSum_spec with h|h <;> simp_all +decide [ isValidCircSegment ];
      obtain ⟨ ⟨ start, hstart, x, hx₁, hx₂, hx₃ ⟩, hx₄ ⟩ := h; use ( start + x ) % nums.size, nums.size - x; simp_all +decide [ circSegmentSum ] ;
      have h_complement_sum : ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! = ∑ k ∈ Finset.range nums.size, nums[k]! - ∑ k ∈ Finset.range x, nums[start + k]! := by
        have h_complement_sum : ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! = ∑ k ∈ Finset.range nums.size, nums[k]! - ∑ k ∈ Finset.range x, nums[(start + k) % nums.size]! := by
          have h_complement_sum : ∑ k ∈ Finset.range nums.size, nums[(start + k) % nums.size]! = ∑ k ∈ Finset.range x, nums[(start + k) % nums.size]! + ∑ k ∈ Finset.range (nums.size - x), nums[(start + x + k) % nums.size]! := by
            rw [ ← Finset.sum_range_add_sum_Ico _ ( show x ≤ nums.size from by linarith ) ] ; simp +decide [ add_assoc, Finset.sum_Ico_eq_sum_range ] ;
          rw [ show ∑ k ∈ Finset.range nums.size, nums[(start + k) % nums.size]! = ∑ k ∈ Finset.range nums.size, nums[k]! from ?_ ] at h_complement_sum ; linarith [ h_complement_sum ] ;
          have h_complement_sum : Finset.image (fun k => (start + k) % nums.size) (Finset.range nums.size) = Finset.range nums.size := by
            refine Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun k hk => Finset.mem_range.mpr <| Nat.mod_lt _ <| by linarith ) ?_ ; rw [ Finset.card_image_of_injOn ] ; intro a ha b hb hab ; simp_all +decide [ Nat.mod_eq_of_lt ] ; exact (by
            exact Nat.mod_eq_of_lt ha ▸ Nat.mod_eq_of_lt hb ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using hab;);
          generalize_proofs at *; (
          conv_rhs => rw [ ← h_complement_sum, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;);
        convert h_complement_sum using 2;
        exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp ‹_› ] ) ] ;
      by_cases h : nums.size ≤ x <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · grind +ring;
      · exact ⟨ ⟨ Nat.mod_lt _ ( by linarith ), Nat.sub_pos_of_lt h ⟩, by simpa [ show i_3 = nums.size by linarith ] using snd_eq.2 ⟩;
    · intro start len h; rcases h with ⟨ h₁, h₂, h₃, h₄ ⟩ ; cases' lt_or_ge ( start + len ) ( nums.size ) with h₅ h₅ <;> simp_all +decide [ circSegmentSum ] ;
      · rw [ ← snd_eq.2 ] ; exact le_trans ( show ∑ k ∈ Finset.range len, nums[ ( start + k ) % nums.size ]! ≤ i_4 from by
                                              convert invariant_inv_maxSum_spec.resolve_left ( by linarith ) |>.2 start len ( by linarith ) h₃ ( by linarith ) using 1 ; rw [ Finset.sum_congr rfl ] ; intros ; rw [ Nat.mod_eq_of_lt ] ; linarith [ Finset.mem_range.mp ‹_› ] ; ) ( by linarith ) ;
      · -- The complement of the current segment is a contiguous subarray of length `nums.size - len`.
        have h_complement : ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! ≥ i_5 := by
          by_cases h₆ : len = nums.size <;> simp_all +decide [ Nat.mod_eq_of_lt ] ; (
          grind);
          -- Since `start + len ≥ nums.size`, we have `(start + len) % nums.size = start + len - nums.size`.
          have h_mod : ∀ j < nums.size - len, (start + len + j) % nums.size = start + len - nums.size + j := by
            intro j hj; rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ Nat.add_comm, Nat.add_sub_assoc h₅ ] ; ring; (
            rw [ Nat.mod_eq_of_lt ( by omega ) ]);
            linarith [ Nat.sub_add_cancel h₄ ]
          generalize_proofs at *; (
          convert invariant_inv_minSum_spec.resolve_left ( by linarith ) |>.2 ( start + len - nums.size ) ( nums.size - len ) _ _ _ using 1 <;> norm_num [ h_mod ] <;> try omega;
          exact Finset.sum_congr rfl fun x hx => by rw [ h_mod x ( Finset.mem_range.mp hx ) ] ;);
        -- The sum of the elements in the current segment is equal to the total sum minus the sum of the complement.
        have h_segment_sum : ∑ i ∈ Finset.range len, nums[(start + i) % nums.size]! = ∑ j ∈ Finset.range nums.size, nums[j]! - ∑ j ∈ Finset.range (nums.size - len), nums[(start + len + j) % nums.size]! := by
          have h_segment_sum : ∑ i ∈ Finset.range nums.size, nums[(start + i) % nums.size]! = ∑ j ∈ Finset.range nums.size, nums[j]! := by
            have h_segment_sum : Finset.image (fun i => (start + i) % nums.size) (Finset.range nums.size) = Finset.range nums.size := by
              refine Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr <| Nat.mod_lt _ h₁ ) ?_;
              rw [ Finset.card_image_of_injOn ];
              intros i hi j hj hij ; simp_all +decide [ Nat.mod_eq_of_lt ];
              exact Nat.mod_eq_of_lt hi ▸ Nat.mod_eq_of_lt hj ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using hij;
            conv_rhs => rw [ ← h_segment_sum, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
          rw [ ← h_segment_sum, ← Finset.sum_range_add_sum_Ico _ ( show len ≤ nums.size from h₄ ) ];
          simp +decide [ add_assoc, Finset.sum_Ico_eq_sum_range ];
        linarith [ show ∑ j ∈ Finset.range nums.size, nums[j]! = total_1 from by rw [ ← snd_eq.2, show i_3 = nums.size from le_antisymm invariant_inv_i_le_n ( by linarith ) ] ]

/-
PROVIDED SOLUTION
postcondition nums i_4 where i_4 = maxSum ≥ 0 and total_1 ≤ i_4 + i_5 (i.e., total - minSum ≤ maxSum). Since i_3 = nums.size.

ACHIEVABILITY: From invariant_inv_maxSum_spec, get start, x with sum = i_4. Use circSegmentSum_non_wrap since start + x ≤ i_3 = nums.size.

MAXIMALITY: For any valid circular segment (s, l):
- If s + l ≤ nums.size (non-wrapping): circSegmentSum = linear sum ≤ i_4 by invariant_inv_maxSum_spec.2.
- If s + l > nums.size (wrapping): The circular sum = total - complement. The complement is a contiguous subarray of length n - l starting at (s + l) % n = s + l - n. complement sum ≥ minSum = i_5 (by invariant_inv_minSum_spec.2 if l < n, since complement has length n - l ≥ 1 and starts at s + l - n < n). So circular sum = total - complement ≤ total_1 - i_5 ≤ i_4 (by if_neg_1: total_1 ≤ i_4 + i_5).
- If l = n (full array): circular sum = total_1 = sum of contiguous subarray of length n ≤ i_4.
-/
theorem goal_59 (nums : Array ℤ) (minSum : ℤ) (i_1 : ℤ) (i_2 : ℤ) (i_3 : ℕ) (i_4 : ℤ) (i_5 : ℤ) (total_1 : ℤ) (invariant_inv_min_le_curMin : minSum ≤ i_2) (invariant_inv_i_le_n : i_3 ≤ nums.size) (invariant_inv_minSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) (invariant_inv_curMax_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_1) ∧ ∀ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! ≤ i_1) (invariant_inv_curMin_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_2) ∧ ∀ start < i_3, i_2 ≤ ∑ k ∈ Finset.range (i_3 - start), nums[start + k]!) (invariant_inv_maxSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = i_4) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4) (require_1 : OfNat.ofNat 0 < nums.size) (if_neg : OfNat.ofNat 0 ≤ i_4) (if_neg_1 : total_1 ≤ i_4 + i_5) (done_1 : nums.size ≤ i_3) (invariant_inv_max_ge_curMax : i_1 ≤ i_4) (snd_eq : minSum = i_5 ∧ ∑ j ∈ Finset.range i_3, nums[j]! = total_1) : postcondition nums i_4 := by
    have h_sum_all : ∑ k ∈ Finset.range i_3, nums[k]! = ∑ k ∈ Finset.range nums.size, nums[k]! := by
      rw [ le_antisymm invariant_inv_i_le_n done_1 ];
    refine' ⟨ _, _ ⟩
    all_goals generalize_proofs at *;
    · rcases invariant_inv_maxSum_spec with h | ⟨ ⟨ start, hstart, x, hx, hx', hx'' ⟩, h ⟩ <;> simp_all +decide [ isValidCircSegment ];
      use start, x; simp_all +decide [ isValidCircSegment, circSegmentSum ] ;
      exact ⟨ ⟨ by linarith, by linarith ⟩, by rw [ ← hx'' ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.mod_eq_of_lt ] ; linarith [ Finset.mem_range.mp ‹_› ] ⟩ ;
    · intros start len h_valid
      by_cases h_wrap : start + len > nums.size
      all_goals generalize_proofs at *;
      · have h_complement : circSegmentSum nums start len = ∑ k ∈ Finset.range nums.size, nums[k]! - ∑ k ∈ Finset.range (nums.size - len), nums[((start + len) % nums.size + k) % nums.size]! := by
          have h_wrap : start + len > nums.size := h_wrap
          have h_len : 1 ≤ len ∧ len ≤ nums.size := by
            exact ⟨ h_valid.2.2.1, h_valid.2.2.2 ⟩
            skip
          convert circSegmentSum_wrap nums start len ( by linarith ) ( by linarith [ h_valid.2.1 ] ) ( by linarith ) ( by linarith ) h_wrap using 1
          skip
        generalize_proofs at *; (
        by_cases h_len_lt : len < nums.size <;> simp_all +decide [ isValidCircSegment ];
        · have h_complement_sum : ∑ k ∈ Finset.range (nums.size - len), nums[((start + len) % nums.size + k) % nums.size]! = ∑ k ∈ Finset.range (nums.size - len), nums[(start + len) % nums.size + k]! := by
            apply Finset.sum_congr rfl
            intro k hk
            generalize_proofs at *; (
            simp +zetaDelta at *;
            rw [ Nat.add_mod, Nat.mod_eq_of_lt ] <;> try linarith [ Nat.sub_add_cancel h_len_lt.le ] ;
            · rw [ Nat.mod_eq_of_lt ( by linarith [ Nat.sub_add_cancel h_len_lt.le ] : k < nums.size ) ];
            · rw [ Nat.mod_eq_sub_mod ] <;> try linarith [ Nat.sub_add_cancel h_len_lt.le ] ;
              rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega;)
          generalize_proofs at *; (
          have h_complement_sum : ∑ k ∈ Finset.range (nums.size - len), nums[(start + len) % nums.size + k]! ≥ i_5 := by
            have h_complement_sum : ∀ start len, start < i_3 → 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≥ i_5 := by
              cases i_3 <;> aesop ( simp_config := { singlePass := true } ) ;
            generalize_proofs at *; (
            convert h_complement_sum ( ( start + len ) % nums.size ) ( nums.size - len ) _ _ _ using 1 <;> norm_num [ Nat.mod_eq_of_lt, h_valid, h_len_lt, h_wrap, done_1 ];
            · exact lt_of_lt_of_le ( Nat.mod_lt _ ( by linarith ) ) ( by linarith );
            · exact Nat.sub_pos_of_lt h_len_lt;
            · rw [ Nat.mod_eq_sub_mod ] <;> try linarith [ Nat.sub_add_cancel h_len_lt.le ] ;
              rw [ Nat.mod_eq_of_lt ] <;> omega;)
          generalize_proofs at *; (
          simp_all +decide [ Nat.mod_eq_of_lt ] ; linarith!;));
        · grind);
      · convert invariant_inv_maxSum_spec.resolve_left ( by linarith [ h_valid.1 ] ) |>.2 start len ( by linarith [ h_valid.1, h_valid.2.1 ] ) ( by linarith [ h_valid.1, h_valid.2.2.1 ] ) ( by linarith [ h_valid.1, h_valid.2.2.2 ] ) using 1
        generalize_proofs at *; (
        exact circSegmentSum_non_wrap nums start len ( by linarith [ h_valid.1 ] ) ( by linarith [ h_valid.2.1 ] ) ( by linarith [ h_valid.2.2.2 ] ) ▸ rfl;)

end Proof