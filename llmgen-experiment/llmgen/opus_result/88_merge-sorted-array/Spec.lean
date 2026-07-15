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

section Specs
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
method MergeSortedArrays (nums1 : Array Int) (nums2 : Array Int)
  return (result : Array Int)
  require precondition nums1 nums2
  ensures postcondition nums1 nums2 result
  do
  pure (#[] : Array Int)  -- placeholder body

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
