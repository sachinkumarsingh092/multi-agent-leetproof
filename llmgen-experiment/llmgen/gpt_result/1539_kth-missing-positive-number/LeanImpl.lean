import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    1539. Kth Missing Positive Number: Given a strictly increasing array of positive integers `arr` and a positive integer `k`, return the k-th positive integer that does not appear in `arr`.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. The input `arr` is an array of natural numbers, intended to represent positive integers.
    2. The array is strictly increasing: each element is less than the next element.
    3. A positive integer `m` is considered “missing” if `m ≥ 1` and `m` is not an element of `arr`.
    4. For any `n ≥ 1`, we can count how many missing positive integers are in the range `[1, n]`.
    5. The desired output `result` is the unique positive integer such that:
       a. `result` is missing from `arr`.
       b. Exactly `k-1` missing positive integers are ≤ `result - 1`.
       c. Exactly `k` missing positive integers are ≤ `result`.
    6. These properties characterize the k-th missing positive integer without prescribing an algorithm.
-/

-- Boolean membership check for arrays of naturals.
-- We use Bool equality (==) to keep this decidable/computable.
def inArrayB (arr : Array Nat) (x : Nat) : Bool :=
  arr.any (fun y => y == x)

-- `arr` is strictly increasing.
def strictlyIncreasing (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! < arr[i + 1]!

-- Every element of `arr` is positive.
def allPositive (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i < arr.size → 0 < arr[i]!

-- Number of missing positive integers in the interval [1, n].
-- This is a computable definition using `Finset.Icc` and filtering by membership in `arr`.
def missingUpTo (arr : Array Nat) (n : Nat) : Nat :=
  ((Finset.Icc (1 : Nat) n).filter (fun m => !(inArrayB arr m))).card

-- Preconditions
-- `k` is positive and `arr` satisfies the problem's input constraints.
def precondition (arr : Array Nat) (k : Nat) : Prop :=
  k > 0 ∧ strictlyIncreasing arr ∧ allPositive arr

-- Postconditions
-- `result` is the k-th missing positive integer:
-- it is missing itself, and the missing-count just below it is k-1 while up to it is k.
def postcondition (arr : Array Nat) (k : Nat) (result : Nat) : Prop :=
  0 < result ∧
  inArrayB arr result = false ∧
  missingUpTo arr (Nat.pred result) = k - 1 ∧
  missingUpTo arr result = k
end Specs

section Impl
def implementation (arr : Array Nat) (k : Nat) : Nat :=
  -- missing count before index i (0-based) is arr[i] - (i+1)
  let n := arr.size
  if h0 : n = 0 then
    k
  else
    let missingAt (i : Nat) : Nat :=
      -- for i < n, arr[i]! is safe; otherwise this value is irrelevant
      arr[i]! - (i + 1)

    -- find the first index where missingAt i ≥ k, in range [lo, hi]
    let rec bs (lo hi : Nat) : Nat :=
      if h : lo < hi then
        let mid := lo + (hi - lo) / 2
        if missingAt mid < k then
          bs (mid + 1) hi
        else
          bs lo mid
      else
        lo
    termination_by hi - lo

    let idx := bs 0 n
    if hidx : idx = 0 then
      -- before the first element, the k-th missing is just k
      k
    else
      -- answer lies after arr[idx-1]
      let prevIdx := idx - 1
      let prevVal := arr[prevIdx]!
      let missPrev := missingAt prevIdx
      prevVal + (k - missPrev)
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [2,3,4,7,11], k = 5 => 9
def test1_arr : Array Nat := #[2, 3, 4, 7, 11]
def test1_k : Nat := 5
def test1_Expected : Nat := 9

-- Test case 2: Example 2
-- arr = [1,2,3,4], k = 2 => 6
def test2_arr : Array Nat := #[1, 2, 3, 4]
def test2_k : Nat := 2
def test2_Expected : Nat := 6

-- Test case 3: Empty array (vacuously strictly increasing); missing positives are [1,2,3,...]
def test3_arr : Array Nat := #[]
def test3_k : Nat := 1
def test3_Expected : Nat := 1

-- Test case 4: Single element not starting at 1
-- arr = [2]; missing positives are [1,3,4,...]
def test4_arr : Array Nat := #[2]
def test4_k : Nat := 1
def test4_Expected : Nat := 1

-- Test case 5: Single element starting at 1
-- arr = [1]; missing positives are [2,3,4,...]
def test5_arr : Array Nat := #[1]
def test5_k : Nat := 1
def test5_Expected : Nat := 2

-- Test case 6: Small gap inside array
-- arr = [1,3]; missing positives are [2,4,5,...]
def test6_arr : Array Nat := #[1, 3]
def test6_k : Nat := 1
def test6_Expected : Nat := 2

-- Test case 7: First few positives missing before the first element
-- arr = [5,6,7]; missing positives are [1,2,3,4,8,9,...]
def test7_arr : Array Nat := #[5, 6, 7]
def test7_k : Nat := 2
def test7_Expected : Nat := 2

-- Test case 8: Large jump later in the array
-- arr = [1,2,100]; missing positives are [3..99] then [101..]
-- 97th missing is 99
def test8_arr : Array Nat := #[1, 2, 100]
def test8_k : Nat := 97
def test8_Expected : Nat := 99

-- Test case 9: Same array as example 1 but smallest valid k
-- missing positives start with 1
def test9_arr : Array Nat := #[2, 3, 4, 7, 11]
def test9_k : Nat := 1
def test9_Expected : Nat := 1
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_arr test1_k), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr test2_k), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr test3_k), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr test4_k), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr test5_k), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr test6_k), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr test7_k), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr test8_k), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr test9_k), test9_Expected]
end Assertions

section Pbt
method implementationPbt (arr : Array Nat) (k : Nat)
  return (result : Nat)
  require precondition arr k
  ensures postcondition arr k result
  do
  return (implementation arr k)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (arr : Array ℕ)
    (k : ℕ)
    (h_precond : precondition arr k)
    (h0 : arr.size = 0)
    : postcondition arr k (implementation arr k) := by
  have hkpos : 0 < k := h_precond.1
  have harr : arr = (#[] : Array ℕ) := Array.eq_empty_of_size_eq_zero (xs := arr) h0
  subst harr
  -- now everything reduces to computation on the empty array
  simp [postcondition, implementation, hkpos, missingUpTo, inArrayB, Nat.pred_eq_sub_one]

lemma inArrayB_eq_true_iff (arr : Array Nat) (x : Nat) :
    inArrayB arr x = true ↔ ∃ (i : Nat) (h : i < arr.size), arr[i] == x := by
  unfold inArrayB
  simpa using (Array.any_eq_true (p := fun y => y == x) (as := arr))

lemma inArrayB_eq_false_iff (arr : Array Nat) (x : Nat) :
    inArrayB arr x = false ↔ ∀ (i : Nat) (h : i < arr.size), ¬ (arr[i] == x) := by
  unfold inArrayB
  simpa using (Array.any_eq_false (p := fun y => y == x) (as := arr))



theorem correctness_goal_1
    (arr : Array ℕ)
    (k : ℕ)
    (h_precond : precondition arr k)
    (h0 : ¬arr.size = 0)
    : postcondition arr k (implementation arr k) := by
    sorry

theorem correctness_goal
    (arr : Array Nat)
    (k : Nat)
    (h_precond : precondition arr k)
    : postcondition arr k (implementation arr k) := by
  classical
  by_cases h0 : arr.size = 0
  · have h_empty : postcondition arr k (implementation arr k) := by
      -- arr is empty so implementation = k
      expose_names; exact (correctness_goal_0 arr k h_precond h0)
    simpa [implementation, h0] using h_empty
  · have h_nonempty : postcondition arr k (implementation arr k) := by
      -- main nonempty correctness
      expose_names; exact (correctness_goal_1 arr k h_precond h0)
    simpa [implementation, h0] using h_nonempty
end Proof
