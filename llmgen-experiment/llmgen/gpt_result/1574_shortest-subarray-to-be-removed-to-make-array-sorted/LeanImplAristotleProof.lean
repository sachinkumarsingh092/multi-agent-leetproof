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
  if h0 : n = 0 then
    0
  else
    -- find the longest nondecreasing prefix
    let rec findLeft (i : Nat) : Nat :=
      if h : i + 1 < n then
        if arr[i]! ≤ arr[i + 1]! then
          findLeft (i + 1)
        else
          i
      else
        i
    termination_by n - i
    -- find the earliest index of a nondecreasing suffix
    let rec findRight (j : Nat) : Nat :=
      if h : 0 < j then
        let j' := j - 1
        if arr[j']! ≤ arr[j]! then
          findRight j'
        else
          j
      else
        0
    termination_by j

    let left := findLeft 0
    if hsorted : left + 1 = n then
      0
    else
      let right := findRight (n - 1)
      -- removing a prefix or suffix as baseline
      let base1 := n - (left + 1)
      let base2 := right

      -- two pointers to merge prefix [0..left] and suffix [right..n)
      let rec merge (i j : Nat) (best : Nat) : Nat :=
        if hi : i ≤ left then
          if hj : j < n then
            if arr[i]! ≤ arr[j]! then
              let removed := j - i - 1
              let best' := Nat.min best removed
              merge (i + 1) j best'
            else
              merge i (j + 1) best
          else
            best
        else
          best
      termination_by (left + 1 - i) + (n - j)

      merge 0 right (Nat.min base1 base2)
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

theorem correctness_goal_1_0 (arr : Array ℤ) (h_precond : precondition arr) (h0 : ¬arr.size = 0) (hsorted : ¬implementation.findLeft arr arr.size 0 + 1 = arr.size) : ∃ l r,
  validRemoval arr l r ∧
    implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
        (implementation.findRight arr (arr.size - 1))
        ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min (implementation.findRight arr (arr.size - 1))) =
      r - l := by
    sorry
end Proof
