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
    674. Longest Continuous Increasing Subsequence: return the length of the longest strictly increasing contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A continuous subsequence is a contiguous subarray determined by a start index `l` and a positive length `len`.
    3. Such a subarray is strictly increasing when each adjacent pair increases: for all valid offsets `i`,
       nums[l+i] < nums[l+i+1].
    4. The output is the maximum length among all strictly increasing contiguous subarrays.
    5. Since a single element is trivially strictly increasing, when the array is non-empty the answer is at least 1.
-/

section Specs
-- A segment starting at `l` with length `len` is within bounds.
def segInBounds (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  l + len ≤ nums.size

-- A segment is required to be non-empty.
def segNonempty (len : Nat) : Prop :=
  1 ≤ len

-- Strictly increasing adjacent condition over a bounded, non-empty segment.
def segStrictlyIncreasing (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  segNonempty len ∧
  segInBounds nums l len ∧
  (∀ (i : Nat), i + 1 < len → nums[l + i]! < nums[l + i + 1]!)

-- Precondition: we follow the common problem constraint that the input array is non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- Postcondition: result is exactly the maximum length of any strictly increasing contiguous segment.
def postcondition (nums : Array Int) (result : Nat) : Prop :=
  result ≥ 1 ∧
  result ≤ nums.size ∧
  (∃ (l : Nat), segStrictlyIncreasing nums l result) ∧
  (∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len → len ≤ result)
end Specs

section Impl
method LongestContinuousIncreasingSubsequence (nums : Array Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
    pure 0

end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [1,3,5,4,7] => longest increasing contiguous subarray is [1,3,5], length 3
def test1_nums : Array Int := #[1, 3, 5, 4, 7]
def test1_Expected : Nat := 3

-- Test case 2: Example 2
-- nums = [2,2,2,2,2] => any strictly increasing contiguous subarray has length 1
def test2_nums : Array Int := #[2, 2, 2, 2, 2]
def test2_Expected : Nat := 1

-- Test case 3: Entire array strictly increasing
def test3_nums : Array Int := #[1, 2, 3, 4]
def test3_Expected : Nat := 4

-- Test case 4: Strictly decreasing array
def test4_nums : Array Int := #[4, 3, 2, 1]
def test4_Expected : Nat := 1

-- Test case 5: Single element
def test5_nums : Array Int := #[10]
def test5_Expected : Nat := 1

-- Test case 6: Includes negative numbers and increasing through zero
def test6_nums : Array Int := #[-3, -2, -1, 0]
def test6_Expected : Nat := 4

-- Test case 7: Increase, then drop, then longer increase
def test7_nums : Array Int := #[1, 3, 2, 4, 5]
def test7_Expected : Nat := 3

-- Test case 8: Equal adjacent elements break strict increase
def test8_nums : Array Int := #[1, 2, 2, 3]
def test8_Expected : Nat := 2

-- Test case 9: Multiple runs, longest at end
def test9_nums : Array Int := #[0, 1, 0, 1, 2, 3]
def test9_Expected : Nat := 4
end TestCases
