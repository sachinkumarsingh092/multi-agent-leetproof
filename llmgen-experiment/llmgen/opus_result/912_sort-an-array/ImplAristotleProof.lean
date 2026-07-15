import Mathlib.Tactic

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    SortAnArray: Given an array of integers, return the same elements sorted in ascending (nondecreasing) order.
    **Important: complexity should be O(n + k) time and O(k) space, where k is the range of values**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. The output is an array of integers with the same length as `nums`.
    3. The output must be sorted in nondecreasing order (ascending with duplicates allowed).
    4. The output must be a permutation of the input: every integer value occurs the same number of times in the output as in the input.
    5. Constraints: 1 ≤ nums.length ≤ 5 * 10^4.
    6. Constraints: each element nums[i] satisfies -5 * 10^4 ≤ nums[i] ≤ 5 * 10^4.
-/

section Specs
-- The allowed value range from the problem constraints.
def minVal : Int := -50000

def maxVal : Int := 50000

-- Array is sorted in nondecreasing order.
def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- All elements satisfy the given inclusive bounds.
def allInRange (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → minVal ≤ arr[i]! ∧ arr[i]! ≤ maxVal

-- Input constraints from the problem statement.
def precondition (nums : Array Int) : Prop :=
  allInRange nums

-- Output requirements: same length, sorted, stays within the required bounds,
-- and has exactly the same multiplicities as the input for every Int value.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  isSortedNondecreasing result ∧
  allInRange result ∧
  (∀ (v : Int), result.count v = nums.count v)
end Specs

section TestCases
-- Test case 1: Example 1
-- Input: [5,2,3,1]
-- Output: [1,2,3,5]
def test1_nums : Array Int := #[5, 2, 3, 1]
def test1_Expected : Array Int := #[1, 2, 3, 5]

-- Test case 2: Example 2 with duplicates
-- Input: [5,1,1,2,0,0]
-- Output: [0,0,1,1,2,5]
def test2_nums : Array Int := #[5, 1, 1, 2, 0, 0]
def test2_Expected : Array Int := #[0, 0, 1, 1, 2, 5]

-- Test case 3: Single element (boundary size)
def test3_nums : Array Int := #[42]
def test3_Expected : Array Int := #[42]

-- Test case 4: Already sorted array (includes negatives and 0)
def test4_nums : Array Int := #[-3, -1, 0, 2, 4]
def test4_Expected : Array Int := #[-3, -1, 0, 2, 4]

-- Test case 5: Reverse sorted array
def test5_nums : Array Int := #[4, 3, 2, 1, 0]
def test5_Expected : Array Int := #[0, 1, 2, 3, 4]

-- Test case 6: All elements equal
def test6_nums : Array Int := #[7, 7, 7, 7]
def test6_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 7: Includes negative numbers and duplicates
def test7_nums : Array Int := #[-1, -5, -1, 3, 0, -5]
def test7_Expected : Array Int := #[-5, -5, -1, -1, 0, 3]

-- Test case 8: Includes min/max constraint boundaries
def test8_nums : Array Int := #[50000, -50000, 0, 50000, -50000]
def test8_Expected : Array Int := #[-50000, -50000, 0, 50000, 50000]

-- Test case 9: Mixed values with repeated zeros
def test9_nums : Array Int := #[0, 2, 0, 1, 2, 0]
def test9_Expected : Array Int := #[0, 0, 0, 1, 2, 2]
end TestCases

section Proof

theorem goal_5 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℤ) (i_2 : ℕ) (j : ℕ) (result : Array ℤ) (invariant_counts_size_2 : i_1.size = OfNat.ofNat 100001) (a_3 : j ≤ OfNat.ofNat 100001) (invariant_result_sorted : ∀ (i j : ℕ), i < j → j < result.size → result[i]! ≤ result[j]!) (invariant_result_in_range : ∀ i < result.size, -OfNat.ofNat 50000 ≤ result[i]! ∧ result[i]! ≤ OfNat.ofNat 50000) (invariant_counts_is_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast) (invariant_result_count_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < j → Array.count v result = Array.count v nums) (invariant_result_upper : ∀ k < result.size, result[k]! ≤ j.cast - OfNat.ofNat 50000) (if_pos : j < OfNat.ofNat 100001) (c : ℤ) (result_1 : Array ℤ) (invariant_c_nonneg : OfNat.ofNat 0 ≤ c) (invariant_inner_sorted : ∀ (i j : ℕ), i < j → j < result_1.size → result_1[i]! ≤ result_1[j]!) (invariant_inner_in_range : ∀ i < result_1.size, -OfNat.ofNat 50000 ≤ result_1[i]! ∧ result_1[i]! ≤ OfNat.ofNat 50000) (invariant_inner_upper : ∀ k < result_1.size, result_1[k]! ≤ j.cast - OfNat.ofNat 50000) (a_5 : j < OfNat.ofNat 100001) (invariant_inner_counts_size : i_1.size = OfNat.ofNat 100001) (invariant_inner_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast) (invariant_inner_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < j → Array.count v result_1 = Array.count v nums) (invariant_inner_partial : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat = j → Array.count v result_1 = (i_1[j]! - c).toNat) (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001) (a_1 : i_2 ≤ nums.size) (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast) (a_2 : True) (invariant_result_count_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → j ≤ (v + OfNat.ofNat 50000).toNat → Array.count v result = OfNat.ofNat 0) (a_4 : True) (invariant_inner_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → j.cast < v + OfNat.ofNat 50000 → Array.count v result_1 = OfNat.ofNat 0) (if_pos_1 : OfNat.ofNat 0 < c) (a : True) (done_1 : nums.size ≤ i_2) : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat = j → Array.count v (result_1.push (j.cast - OfNat.ofNat 50000)) = (i_1[j]! - (c - OfNat.ofNat 1)).toNat := by
        sorry

theorem goal_6 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℤ) (i_2 : ℕ) (j : ℕ) (result : Array ℤ) (invariant_counts_size_2 : i_1.size = OfNat.ofNat 100001) (a_3 : j ≤ OfNat.ofNat 100001) (invariant_result_sorted : ∀ (i j : ℕ), i < j → j < result.size → result[i]! ≤ result[j]!) (invariant_result_in_range : ∀ i < result.size, -OfNat.ofNat 50000 ≤ result[i]! ∧ result[i]! ≤ OfNat.ofNat 50000) (invariant_counts_is_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast) (invariant_result_count_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < j → Array.count v result = Array.count v nums) (invariant_result_upper : ∀ k < result.size, result[k]! ≤ j.cast - OfNat.ofNat 50000) (if_pos : j < OfNat.ofNat 100001) (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001) (a_1 : i_2 ≤ nums.size) (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast) (a_2 : True) (invariant_result_count_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → j ≤ (v + OfNat.ofNat 50000).toNat → Array.count v result = OfNat.ofNat 0) (a : True) (done_1 : nums.size ≤ i_2) : OfNat.ofNat 0 ≤ i_1[j]! := by
        sorry

theorem goal_7 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℤ) (i_2 : ℕ) (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001) (a_1 : i_2 ≤ nums.size) (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast) (a : True) (done_1 : nums.size ≤ i_2) : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast := by
        sorry

theorem goal_8 (nums : Array ℤ) (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000) (i_1 : Array ℤ) (i_2 : ℕ) (invariant_counts_size_2 : i_1.size = OfNat.ofNat 100001) (invariant_counts_is_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast) (i_4 : ℕ) (result_1 : Array ℤ) (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001) (a_1 : i_2 ≤ nums.size) (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast) (a_3 : i_4 ≤ OfNat.ofNat 100001) (invariant_result_sorted : ∀ (i j : ℕ), i < j → j < result_1.size → result_1[i]! ≤ result_1[j]!) (invariant_result_in_range : ∀ i < result_1.size, -OfNat.ofNat 50000 ≤ result_1[i]! ∧ result_1[i]! ≤ OfNat.ofNat 50000) (invariant_result_count_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < i_4 → Array.count v result_1 = Array.count v nums) (invariant_result_upper : ∀ k < result_1.size, result_1[k]! ≤ i_4.cast - OfNat.ofNat 50000) (a : True) (done_1 : nums.size ≤ i_2) (a_2 : True) (done_2 : OfNat.ofNat 100001 ≤ i_4) (invariant_result_count_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_4 ≤ (v + OfNat.ofNat 50000).toNat → Array.count v result_1 = OfNat.ofNat 0) : postcondition nums result_1 := by
        sorry
end Proof
