import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Impl
method MaxSumCircularSubarray (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

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
