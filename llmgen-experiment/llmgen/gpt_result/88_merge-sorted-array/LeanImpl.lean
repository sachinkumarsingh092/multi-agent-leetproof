import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    MergeSortedArrays: Merge two sorted integer arrays into a new sorted array.
    Natural language breakdown:
    1. Inputs are two arrays of integers, `nums1` and `nums2`.
    2. Each input array is sorted in non-decreasing order.
    3. The output is a new array whose length is `nums1.size + nums2.size`.
    4. The output is sorted in non-decreasing order.
    5. The output contains exactly the multiset union of elements of `nums1` and `nums2`:
       for every integer value, its number of occurrences in the output equals the sum of its
       occurrences in the two inputs.
    6. Edge cases include empty inputs, singleton inputs, duplicates, and negative values.
    Your algorithm should run in **O(m+n)** time and **O(m+n)** extra space, where m = nums1.size and n = nums2.size.
-/

-- Helper predicate: an array is sorted in non-decreasing order.
-- We use adjacent comparisons (local sortedness) for a simple, index-based formulation.
def sortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Helper function: count occurrences of a value in an array.
def countInArray (a : Array Int) (v : Int) : Nat :=
  a.toList.count v

-- Preconditions: both input arrays are sorted in non-decreasing order.
def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  sortedNondecreasing nums1 ∧ sortedNondecreasing nums2

-- Postconditions: result has the correct size, is sorted, and contains exactly all elements.
def postcondition (nums1 : Array Int) (nums2 : Array Int) (result : Array Int) : Prop :=
  result.size = nums1.size + nums2.size ∧
  sortedNondecreasing result ∧
  ∀ v : Int, countInArray result v = countInArray nums1 v + countInArray nums2 v
end Specs

section Impl
def implementation (nums1 : Array Int) (nums2 : Array Int) : Array Int :=
  -- Pure functional linear-time merge using index recursion.
  let rec go (i j : Nat) (acc : Array Int) : Array Int :=
    if hi : i < nums1.size then
      if hj : j < nums2.size then
        let x := nums1[i]!
        let y := nums2[j]!
        if x ≤ y then
          go (i + 1) j (acc.push x)
        else
          go i (j + 1) (acc.push y)
      else
        -- nums2 exhausted; drain the rest of nums1
        let rec drain1 (k : Nat) (acc : Array Int) : Array Int :=
          if hk : k < nums1.size then
            drain1 (k + 1) (acc.push (nums1[k]!))
          else
            acc
        drain1 i acc
    else
      if hj : j < nums2.size then
        -- nums1 exhausted; drain the rest of nums2
        let rec drain2 (k : Nat) (acc : Array Int) : Array Int :=
          if hk : k < nums2.size then
            drain2 (k + 1) (acc.push (nums2[k]!))
          else
            acc
        drain2 j acc
      else
        acc
  go 0 0 #[]
termination_by
  (nums1.size - i) + (nums2.size - j)
end Impl

section TestCases
-- Test case 1: Example 1
-- nums1 = [1,2,3], nums2 = [2,5,6] => [1,2,2,3,5,6]
def test1_nums1 : Array Int := #[1, 2, 3]
def test1_nums2 : Array Int := #[2, 5, 6]
def test1_Expected : Array Int := #[1, 2, 2, 3, 5, 6]

-- Test case 2: Example 2
-- nums1 = [1], nums2 = [] => [1]
def test2_nums1 : Array Int := #[1]
def test2_nums2 : Array Int := #[]
def test2_Expected : Array Int := #[1]

-- Test case 3: Example 3
-- nums1 = [], nums2 = [1] => [1]
def test3_nums1 : Array Int := #[]
def test3_nums2 : Array Int := #[1]
def test3_Expected : Array Int := #[1]

-- Test case 4: Both empty
-- [] and [] => []
def test4_nums1 : Array Int := #[]
def test4_nums2 : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: Duplicates across both arrays
-- [1,1,1] and [1,1] => [1,1,1,1,1]
def test5_nums1 : Array Int := #[1, 1, 1]
def test5_nums2 : Array Int := #[1, 1]
def test5_Expected : Array Int := #[1, 1, 1, 1, 1]

-- Test case 6: Negative values and mix
-- [-3,-1,2] and [-2,0,3] => [-3,-2,-1,0,2,3]
def test6_nums1 : Array Int := #[-3, -1, 2]
def test6_nums2 : Array Int := #[-2, 0, 3]
def test6_Expected : Array Int := #[-3, -2, -1, 0, 2, 3]

-- Test case 7: Already separated ranges
-- [1,2,3] and [4,5] => [1,2,3,4,5]
def test7_nums1 : Array Int := #[1, 2, 3]
def test7_nums2 : Array Int := #[4, 5]
def test7_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 8: Interleaving with equal boundary values and many duplicates
-- [0,2,2,2] and [2,2,3] => [0,2,2,2,2,2,3]
def test8_nums1 : Array Int := #[0, 2, 2, 2]
def test8_nums2 : Array Int := #[2, 2, 3]
def test8_Expected : Array Int := #[0, 2, 2, 2, 2, 2, 3]

-- Test case 9: Singleton + singleton with ordering
-- [0] and [1] => [0,1]
def test9_nums1 : Array Int := #[0]
def test9_nums2 : Array Int := #[1]
def test9_Expected : Array Int := #[0, 1]
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums1 test1_nums2), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums1 test2_nums2), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums1 test3_nums2), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums1 test4_nums2), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums1 test5_nums2), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums1 test6_nums2), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums1 test7_nums2), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums1 test8_nums2), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums1 test9_nums2), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (nums1 : Array Int)
    (nums2 : Array Int)
    (h_precond : precondition nums1 nums2)
    : postcondition nums1 nums2 (implementation nums1 nums2) := by
    sorry
end Proof
