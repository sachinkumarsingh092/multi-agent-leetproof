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

section Impl
private def repeatPush (arr : Array Int) (val : Int) (count : Nat) : Array Int :=
  match count with
  | 0 => arr
  | n + 1 => repeatPush (arr.push val) val n

def implementation (nums : Array Int) : Array Int :=
  -- Counting sort: O(n + k) time, O(k) space
  -- Range: -50000 to 50000, so k = 100001
  let k : Nat := 100001
  let offset : Int := 50000
  -- Build count array
  let counts := nums.foldl (fun (acc : Array Nat) (v : Int) =>
    let idx := (v + offset).toNat
    acc.modify idx (· + 1)
  ) (mkArray k 0)
  -- Build result by iterating over count array
  let (result, _) := counts.foldl (fun (acc : Array Int × Nat) (c : Nat) =>
    let (arr, idx) := acc
    let val : Int := (Int.ofNat idx) - offset
    let arr' := repeatPush arr val c
    (arr', idx + 1)
  ) (#[], 0)
  result
end Impl

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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
private theorem repeatPush_size (arr : Array Int) (val : Int) (count : Nat) :
    (repeatPush arr val count).size = arr.size + count := by
  induction count generalizing arr with
  | zero => simp [repeatPush]
  | succ n ih =>
    simp [repeatPush]
    rw [ih]
    rw [Array.size_push]
    omega


theorem correctness_goal_0_0
    (nums : Array ℤ)
    : (Array.foldl
      (fun acc v =>
        let idx := (v + 50000).toNat;
        acc.modify idx fun x => x + 1)
      (mkArray 100001 0) nums).size =
  100001 := by
    have h := Array.foldl_induction (as := nums)
      (motive := fun _ (acc : Array Nat) => acc.size = 100001)
      (init := mkArray 100001 0)
      (f := fun acc v => let idx := (v + 50000).toNat; acc.modify idx (· + 1))
      (by native_decide)
      (by intro i b hb; simp [Array.size_modify, hb])
    exact h
end Proof
