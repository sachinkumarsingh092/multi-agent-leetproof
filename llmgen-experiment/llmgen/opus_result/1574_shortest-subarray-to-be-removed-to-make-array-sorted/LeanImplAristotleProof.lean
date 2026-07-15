import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (arr : Array Int) : Nat :=
  let n := arr.size
  if n ≤ 1 then 0
  else
    -- Find longest non-decreasing prefix: find first index where arr[i] > arr[i+1]
    let rec findPrefixEnd (i : Nat) : Nat :=
      if h : i + 1 < n then
        if arr[i]! ≤ arr[i + 1]! then findPrefixEnd (i + 1)
        else i
      else i
    termination_by n - i
    let prefixEnd := findPrefixEnd 0  -- last index of non-decreasing prefix

    -- If entire array is non-decreasing
    if prefixEnd == n - 1 then 0
    else
      -- Find longest non-decreasing suffix: find last index where arr[i-1] > arr[i]
      let rec findSuffixStart (j : Nat) : Nat :=
        if h : j = 0 then 0
        else if arr[j - 1]! ≤ arr[j]! then findSuffixStart (j - 1)
        else j
      termination_by j
      decreasing_by omega
      let suffixStart := findSuffixStart (n - 1)  -- first index of non-decreasing suffix

      -- Option 1: keep only prefix (remove from prefixEnd+1 to end)
      let ans1 := n - (prefixEnd + 1)
      -- Option 2: keep only suffix (remove from 0 to suffixStart)
      let ans2 := suffixStart
      let initAns := min ans1 ans2

      -- Option 3: merge prefix and suffix using two pointers
      -- i scans prefix [0..prefixEnd], j scans suffix [suffixStart..n-1]
      -- We want arr[i] <= arr[j], and remove (i+1)..(j-1), length = j - i - 1
      let rec merge (i j best : Nat) : Nat :=
        if h1 : i > prefixEnd then best
        else if h2 : j ≥ n then best
        else
          if arr[i]! ≤ arr[j]! then
            let removal := j - (i + 1)
            let best' := min best removal
            merge (i + 1) j best'
          else
            merge i (j + 1) best
      termination_by (prefixEnd + 1 - i) + (n - j)
      decreasing_by all_goals omega
      merge 0 suffixStart initAns
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

section Proof

theorem correctness_goal_0_2 (arr : Array ℤ) (h_precond : precondition arr) (h_valid_all : validRemoval arr 0 arr.size) (h_small_sorted : arr.size ≤ 1 → isNondecreasing arr) : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l := by
    sorry

theorem correctness_goal_1_2 (arr : Array ℤ) (h_precond : precondition arr) (h_exists : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l) (l : ℕ) (r : ℕ) (hvalid : validRemoval arr l r) (h_small : ¬arr.size ≤ 1) (h_sorted : ¬(implementation.findPrefixEnd arr arr.size 0 == arr.size - 1) = true) : implementation arr ≤ r - l := by
    sorry
end Proof
