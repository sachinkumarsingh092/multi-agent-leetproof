import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MaximumSubarray: return the maximum possible sum of a non-empty contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A contiguous subarray is determined by indices `start` and `stop` with `start < stop`.
    3. The sum of a subarray is the sum of the elements in `nums[start:stop]`.
    4. The result is the sum of some non-empty contiguous subarray (achievability).
    5. The result is greater than or equal to the sum of every non-empty contiguous subarray (maximality).
    6. The input must be non-empty so that at least one non-empty subarray exists.
-/

section Specs
-- Sum of all elements in an array.
def arraySum (arr : Array Int) : Int :=
  arr.foldl (fun acc x => acc + x) 0

-- Sum of the contiguous segment nums[start:stop].
-- This uses Array.extract; the spec restricts start/stop so no clamping occurs.
def rangeSum (nums : Array Int) (start : Nat) (stop : Nat) : Int :=
  arraySum (nums.extract start stop)

-- Input must be non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- result is the maximum sum among all non-empty contiguous subarrays.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size ∧ rangeSum nums start stop = result) ∧
  (∀ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size → rangeSum nums start stop ≤ result)
end Specs

section Impl
method MaximumSubarray (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [-2,1,-3,4,-1,2,1,-5,4] => 6 (subarray [4,-1,2,1])
def test1_nums : Array Int := #[-2, 1, -3, 4, -1, 2, 1, -5, 4]
def test1_Expected : Int := 6

-- Test case 2: Example 2 (single element)
def test2_nums : Array Int := #[1]
def test2_Expected : Int := 1

-- Test case 3: Example 3 (whole array is best)
def test3_nums : Array Int := #[5, 4, -1, 7, 8]
def test3_Expected : Int := 23

-- Test case 4: All negative (best is the least negative single element)
def test4_nums : Array Int := #[-8, -3, -6, -2, -5, -4]
def test4_Expected : Int := -2

-- Test case 5: Contains zeros; best is 0 (choose [0])
def test5_nums : Array Int := #[0, -1, 0, -2]
def test5_Expected : Int := 0

-- Test case 6: Mixed, best is a suffix/prefix segment
-- Best subarray is [3, -1, 2] with sum 4

def test6_nums : Array Int := #[-2, 3, -1, 2, -1]
def test6_Expected : Int := 4

-- Test case 7: Alternating small values
-- Best subarray is [1, -1, 1, -1, 1] has max 1 (any single 1)
def test7_nums : Array Int := #[1, -1, 1, -1, 1]
def test7_Expected : Int := 1

-- Test case 8: Best is the entire array

def test8_nums : Array Int := #[2, 3, 1]
def test8_Expected : Int := 6

-- Test case 9: Two elements, decreasing
-- Best is [10] not [10,-20]
def test9_nums : Array Int := #[10, -20]
def test9_Expected : Int := 10
end TestCases
