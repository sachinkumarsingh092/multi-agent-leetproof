import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_arr), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr), test9_Expected]
end Assertions

section Pbt
-- Lean wrapper for velvet_plausible_test failed to compile. Giving up on PBT.

-- method implementationPbt (arr : Array Int)
--   return (result : Nat)
--   require precondition arr
--   ensures postcondition arr result
--   do
--   return (implementation arr)

-- velvet_plausible_test implementationPbt (config := { maxMs := some 5000 })
end Pbt

section Proof
theorem correctness_goal_0
    (arr : Array ℤ)
    (hsorted : implementation.findLeft arr arr.size 0 + 1 = arr.size)
    : isNondecreasing arr := by
  classical
  unfold isNondecreasing
  set n : Nat := arr.size
  have hn : n = arr.size := rfl

  have hsorted' : implementation.findLeft arr n 0 + 1 = n := by
    simpa [hn] using hsorted

  have hleft0 : implementation.findLeft arr n 0 = n - 1 := by
    exact Nat.eq_sub_of_add_eq hsorted'

  have hstep :
      ∀ i : Nat,
        i + 1 < n →
          implementation.findLeft arr n i = n - 1 →
            arr[i]! ≤ arr[i + 1]! ∧ implementation.findLeft arr n (i + 1) = n - 1 := by
    intro i hi hFi

    -- `i` cannot be the last index when `i+1 < n`
    have hi_le_pred : i + 1 ≤ Nat.pred n := Nat.le_pred_of_lt hi
    have hi_lt_pred : i < Nat.pred n :=
      lt_of_lt_of_le (Nat.lt_succ_self i) hi_le_pred
    have hi_ne_last : i ≠ n - 1 := by
      intro hEq
      -- rewrite `n-1` as `pred n`
      have : i = Nat.pred n := hEq.trans (Nat.sub_one n)
      exact (ne_of_lt hi_lt_pred) this

    by_cases hcmp : arr[i]! ≤ arr[i + 1]!
    · -- unfold one step and simplify the `if`s
      have hFi' := hFi
      unfold implementation.findLeft at hFi'
      -- now the branch must be the recursive one
      have hNext : implementation.findLeft arr n (i + 1) = n - 1 := by
        simpa [hi, hcmp] using hFi'
      exact ⟨hcmp, hNext⟩
    · -- unfolding gives `i = n-1`, contradiction
      have hFi' := hFi
      unfold implementation.findLeft at hFi'
      have : i = n - 1 := by
        simpa [hi, hcmp] using hFi'
      exact (hi_ne_last this).elim

  -- `findLeft` returns `n-1` at every index `< n`
  have hFi : ∀ i : Nat, i < n → implementation.findLeft arr n i = n - 1 := by
    intro i hi
    induction i with
    | zero =>
        simpa using hleft0
    | succ i ih =>
        have hi' : i + 1 < n := by
          simpa [Nat.succ_eq_add_one] using hi
        have hi0 : i < n := lt_trans (Nat.lt_succ_self i) hi'
        have hPrev : implementation.findLeft arr n i = n - 1 := ih hi0
        have hNext : implementation.findLeft arr n (i + 1) = n - 1 := (hstep i hi' hPrev).2
        simpa [Nat.succ_eq_add_one] using hNext

  intro i hi
  have hi0 : i < n := lt_trans (Nat.lt_succ_self i) (by simpa [hn] using hi)
  have hFi0 : implementation.findLeft arr n i = n - 1 := hFi i hi0
  have hle : arr[i]! ≤ arr[i + 1]! := (hstep i (by simpa [hn] using hi) hFi0).1
  simpa [hn] using hle

theorem correctness_goal_1_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h0 : ¬arr.size = 0)
    (hsorted : ¬implementation.findLeft arr arr.size 0 + 1 = arr.size)
    : ∃ l r,
  validRemoval arr l r ∧
    implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
        (implementation.findRight arr (arr.size - 1))
        ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min (implementation.findRight arr (arr.size - 1))) =
      r - l := by
    sorry

theorem correctness_goal_1_1
    (arr : Array ℤ)
    : ∀ (l r : ℕ),
  validRemoval arr l r →
    implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
        (implementation.findRight arr (arr.size - 1))
        ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min (implementation.findRight arr (arr.size - 1))) ≤
      r - l := by
  intro l r hvr
  apply?

theorem correctness_goal_1
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h0 : ¬arr.size = 0)
    (hsorted : ¬implementation.findLeft arr arr.size 0 + 1 = arr.size)
    : postcondition arr
  (implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
    (implementation.findRight arr (arr.size - 1))
    ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min (implementation.findRight arr (arr.size - 1)))) := by
  classical
  refine And.intro ?h_exist ?h_min
  · -- existence of an optimal removal length equal to the merge result
    have h_exist :
        ∃ l r,
          validRemoval arr l r ∧
            implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
                (implementation.findRight arr (arr.size - 1))
                ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min
                  (implementation.findRight arr (arr.size - 1))) =
              r - l := by
      expose_names; exact (correctness_goal_1_0 arr h_precond h0 hsorted)
    simpa [postcondition] using h_exist
  · -- minimality
    have h_min :
        ∀ l r,
          validRemoval arr l r →
            implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
                (implementation.findRight arr (arr.size - 1))
                ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min
                  (implementation.findRight arr (arr.size - 1))) ≤
              r - l := by
      expose_names; exact (correctness_goal_1_1 arr)
    simpa [postcondition] using h_min

theorem correctness_goal
    (arr : Array Int)
    (h_precond : precondition arr)
    : postcondition arr (implementation arr) := by
  classical
  simp [precondition] at h_precond
  by_cases h0 : arr.size = 0
  · simp [implementation, h0, postcondition, validRemoval, removeSubarray, isNondecreasing]
  · -- nonempty
    -- unfold implementation to expose its top-level ifs
    simp [implementation, h0]
    -- now the result is an `if` over `findLeft ... + 1 = arr.size`
    by_cases hsorted : implementation.findLeft arr arr.size 0 + 1 = arr.size
    · -- simplify the goal to result = 0
      simp [hsorted]
      -- We need that `hsorted` implies the array is nondecreasing.
      have h_arr_sorted : isNondecreasing arr := by
        expose_names; exact (correctness_goal_0 arr hsorted)
      unfold postcondition
      constructor
      · refine ⟨0, 0, ?_, by simp⟩
        unfold validRemoval
        refine And.intro (by omega) (And.intro (by omega) ?_)
        simpa [removeSubarray] using h_arr_sorted
      · intro l r hvr
        exact Nat.zero_le _
    · -- main branch
      simp [hsorted]
      -- core correctness for the merge expression
      have h_merge_post :
          postcondition arr
            (implementation.merge arr arr.size (implementation.findLeft arr arr.size 0) 0
              (implementation.findRight arr (arr.size - 1))
              ((arr.size - (implementation.findLeft arr arr.size 0 + 1)).min
                (implementation.findRight arr (arr.size - 1)))) := by
        expose_names; exact (correctness_goal_1 arr h_precond h0 hsorted)
      simpa using h_merge_post
end Proof
