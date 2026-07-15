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
    ShortestSubarrayToRemoveToMakeArraySorted: Given an integer array, remove a contiguous subarray
    (possibly empty) so that the remaining elements are non-decreasing, and return the minimum
    removed length.

    Natural language breakdown:
    1. Input is an array of integers `arr`.
    2. We may remove a contiguous subarray `arr[l..r)` (with 0 ≤ l ≤ r ≤ n). The removed subarray
       can be empty (l = r) and can also be the whole array.
    3. After removing `arr[l..r)`, the remaining elements preserve their relative order and form
       the concatenation of the prefix `arr[0..l)` and suffix `arr[r..n)`.
    4. The remaining array must be non-decreasing: for every adjacent pair of elements,
       the earlier element is ≤ the later element.
    5. The result is the minimum possible length (r - l) among all valid removals.
    6. Edge cases:
       - Already non-decreasing arrays allow removing the empty subarray, so the answer can be 0.
       - Empty array is already non-decreasing, so answer is 0.
       - If the array is strictly decreasing, we can keep at most one element, so the answer is n-1.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: non-decreasing predicate over adjacent indices.
def isNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! ≤ arr[i + 1]!

-- Helper: the array resulting from removing the half-open interval [l, r).
def removeSubarray (arr : Array Int) (l : Nat) (r : Nat) : Array Int :=
  arr.extract 0 l ++ arr.extract r arr.size

-- Helper: a removal is valid when indices are in range and the remaining array is non-decreasing.
def validRemoval (arr : Array Int) (l : Nat) (r : Nat) : Prop :=
  l ≤ r ∧ r ≤ arr.size ∧ isNondecreasing (removeSubarray arr l r)

-- Precondition: no restrictions; empty removals are allowed, so every array has an answer.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the minimum possible removed length among all valid removals.
def postcondition (arr : Array Int) (result : Nat) : Prop :=
  (∃ (l : Nat) (r : Nat), validRemoval arr l r ∧ result = r - l) ∧
  (∀ (l : Nat) (r : Nat), validRemoval arr l r → result ≤ r - l)
end Specs

section Impl
method ShortestSubarrayToRemoveToMakeArraySorted (arr : Array Int)
  return (result : Nat)
  require precondition arr
  ensures postcondition arr result
  do
    if arr.size <= 1 then
      return 0
    else
      -- Step 1: Find longest non-decreasing prefix
      let mut left := 0
      while left + 1 < arr.size
        -- left stays within array bounds
        invariant "prefix_bound" left < arr.size
        -- prefix arr[0..left] is non-decreasing
        invariant "prefix_sorted" ∀ k, k + 1 ≤ left → arr[k]! ≤ arr[k + 1]!
        -- loop exits either normally or via break when a descent is found
        done_with left + 1 ≥ arr.size ∨ arr[left + 1]! < arr[left]!
        decreasing arr.size - left
      do
        if arr[left]! <= arr[left + 1]! then
          left := left + 1
        else
          break

      -- If the whole array is non-decreasing
      if left = arr.size - 1 then
        return 0
      else
        -- Step 2: Find longest non-decreasing suffix
        let mut right := arr.size - 1
        while right > 0
          -- right stays within array bounds
          invariant "suffix_bound" right < arr.size
          -- suffix arr[right..arr.size-1] is non-decreasing
          invariant "suffix_sorted" ∀ k, right ≤ k ∧ k + 1 < arr.size → arr[k]! ≤ arr[k + 1]!
          -- loop exits normally or via break when a descent is found
          done_with right = 0 ∨ arr[right]! < arr[right - 1]!
          decreasing right
        do
          if arr[right - 1]! <= arr[right]! then
            right := right - 1
          else
            break

        -- Step 3: Consider removing everything except the prefix or except the suffix
        -- Remove [left+1 .. arr.size): length = arr.size - left - 1
        -- Remove [0 .. right): length = right
        let mut ans := arr.size - left - 1
        if right < ans then
          ans := right

        -- Step 4: Two-pointer merge of prefix and suffix
        let mut i := 0
        let mut j := right
        while i <= left
          -- i is bounded
          invariant "outer_i_bound" i ≤ left + 1
          -- j stays within bounds (monotonically advances from right, never past arr.size)
          invariant "outer_j_lower" right ≤ j
          invariant "outer_j_upper" j ≤ arr.size
          -- prefix property preserved (arr is immutable)
          invariant "outer_prefix" ∀ k, k + 1 ≤ left → arr[k]! ≤ arr[k + 1]!
          -- suffix property preserved (arr is immutable)
          invariant "outer_suffix" ∀ k, right ≤ k ∧ k + 1 < arr.size → arr[k]! ≤ arr[k + 1]!
          decreasing left + 1 - i
        do
          -- Advance j until arr[i] <= arr[j] or j goes past end
          while j < arr.size
            -- j stays within bounds
            invariant "inner_j_bound" j ≤ arr.size
            -- j never goes below right (only increments); needed to preserve outer_j_lower
            invariant "inner_j_lower" right ≤ j
            -- exit when j out of range or arr[i] <= arr[j]
            done_with j ≥ arr.size ∨ arr[i]! ≤ arr[j]!
            decreasing arr.size - j
          do
            if arr[i]! <= arr[j]! then
              break
            else
              j := j + 1

          -- If we found a valid j
          if j < arr.size then
            -- removal is [i+1 .. j), length = j - i - 1
            let removal := j - i - 1
            if removal < ans then
              ans := removal
          i := i + 1

        return ans
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [1,2,3,10,4,2,3,5] => expected 3
-- One optimal removal is [10,4,2].
def test1_arr : Array Int := #[1, 2, 3, 10, 4, 2, 3, 5]
def test1_Expected : Nat := 3

-- Test case 2: Example 2 (strictly decreasing)
-- arr = [5,4,3,2,1] => expected 4

def test2_arr : Array Int := #[5, 4, 3, 2, 1]
def test2_Expected : Nat := 4

-- Test case 3: Example 3 (already sorted)
-- arr = [1,2,3] => expected 0

def test3_arr : Array Int := #[1, 2, 3]
def test3_Expected : Nat := 0

-- Test case 4: Empty array (degenerate)
-- Already non-decreasing; remove nothing.

def test4_arr : Array Int := #[]
def test4_Expected : Nat := 0

-- Test case 5: Singleton array
-- Already non-decreasing.

def test5_arr : Array Int := #[42]
def test5_Expected : Nat := 0

-- Test case 6: Two elements already non-decreasing

def test6_arr : Array Int := #[1, 1]
def test6_Expected : Nat := 0

-- Test case 7: Two elements decreasing
-- Must remove one element.

def test7_arr : Array Int := #[2, 1]
def test7_Expected : Nat := 1

-- Test case 8: Needs removal in the middle; minimal is 1 (remove the 3)
-- [1,2,3,2,4] -> remove [3] gives [1,2,2,4]

def test8_arr : Array Int := #[1, 2, 3, 2, 4]
def test8_Expected : Nat := 1

-- Test case 9: Remove a prefix to become sorted; minimal is 2
-- [3,4,1,2] -> remove [3,4] leaves [1,2]

def test9_arr : Array Int := #[3, 4, 1, 2]
def test9_Expected : Nat := 2
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((ShortestSubarrayToRemoveToMakeArraySorted test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test ShortestSubarrayToRemoveToMakeArraySorted (config := { maxMs := some 5000 })
end Pbt
