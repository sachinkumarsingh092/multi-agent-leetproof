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
  let mut i := 0
  let mut j := 0
  let mut res : Array Int := #[]
  -- Main merge loop: pick the smaller of the two current elements
  while i < nums1.size ∧ j < nums2.size
    -- i is bounded by nums1.size
    -- Init: i=0 ≤ nums1.size. Pres: i increments by 1 only when i < nums1.size.
    invariant "i_bound" i ≤ nums1.size
    -- j is bounded by nums2.size
    -- Init: j=0 ≤ nums2.size. Pres: j increments by 1 only when j < nums2.size.
    invariant "j_bound" j ≤ nums2.size
    -- res size equals i + j (each iteration pushes one element and increments one index)
    -- Init: res.size=0, i=0, j=0. Pres: push increases size by 1, one of i/j increases by 1.
    invariant "res_size" res.size = i + j
    -- res stays sorted throughout the merge
    -- Init: empty array is sorted. Pres: we push elements ≤ next remaining, maintaining order.
    invariant "res_sorted" sortedNondecreasing res
    -- count preservation: res has exactly elements from nums1[0..i] and nums2[0..j]
    -- Init: all counts are 0. Pres: pushing nums1[i] or nums2[j] updates counts correctly.
    invariant "count_pres" ∀ v : Int, countInArray res v = countInArray (nums1.extract 0 i) v + countInArray (nums2.extract 0 j) v
    -- last element of res ≤ nums1[i] (needed to maintain sortedness when pushing from nums1)
    -- Pres: if we pushed nums1[i], new last = nums1[i] ≤ nums1[i+1] by sorted input.
    --        if we pushed nums2[j], new last = nums2[j] ≤ nums1[i] because we took the smaller.
    invariant "last_le_nums1" (res.size > 0 ∧ i < nums1.size) → res[res.size - 1]! ≤ nums1[i]!
    -- last element of res ≤ nums2[j] (needed to maintain sortedness when pushing from nums2)
    invariant "last_le_nums2" (res.size > 0 ∧ j < nums2.size) → res[res.size - 1]! ≤ nums2[j]!
    -- Decreasing: total remaining elements decreases each iteration
    decreasing nums1.size + nums2.size - i - j
  do
    if nums1[i]! <= nums2[j]! then
      res := res.push nums1[i]!
      i := i + 1
    else
      res := res.push nums2[j]!
      j := j + 1
  -- Copy remaining elements from nums1
  while i < nums1.size
    -- Bounds on i and j carried from loop 1 exit
    invariant "i_bound2" i ≤ nums1.size
    invariant "j_bound2" j ≤ nums2.size
    -- res size still equals i + j
    invariant "res_size2" res.size = i + j
    -- res remains sorted
    invariant "res_sorted2" sortedNondecreasing res
    -- count preservation continues
    invariant "count_pres2" ∀ v : Int, countInArray res v = countInArray (nums1.extract 0 i) v + countInArray (nums2.extract 0 j) v
    -- last element ≤ nums1[i] for sortedness when pushing
    invariant "last_le_nums1_2" (res.size > 0 ∧ i < nums1.size) → res[res.size - 1]! ≤ nums1[i]!
    -- last element ≤ nums2[j]: vacuously true when j ≥ nums2.size (which holds because
    -- if j < nums2.size then loop 1 exited with i ≥ nums1.size so loop 2 doesn't run)
    -- Needed to initialize loop 3's last_le_nums2_3
    invariant "last_le_nums2_2" (res.size > 0 ∧ j < nums2.size) → res[res.size - 1]! ≤ nums2[j]!
    -- j is done (from loop 1 exit condition) or loop doesn't execute
    invariant "j_done" j = nums2.size ∨ ¬(i < nums1.size)
    -- Decreasing: remaining nums1 elements
    decreasing nums1.size - i
  do
    res := res.push nums1[i]!
    i := i + 1
  -- Copy remaining elements from nums2
  while j < nums2.size
    -- Bounds carried forward
    invariant "i_bound3" i ≤ nums1.size
    invariant "j_bound3" j ≤ nums2.size
    -- res size still equals i + j
    invariant "res_size3" res.size = i + j
    -- res remains sorted
    invariant "res_sorted3" sortedNondecreasing res
    -- count preservation continues
    invariant "count_pres3" ∀ v : Int, countInArray res v = countInArray (nums1.extract 0 i) v + countInArray (nums2.extract 0 j) v
    -- last element ≤ nums2[j] for sortedness when pushing
    invariant "last_le_nums2_3" (res.size > 0 ∧ j < nums2.size) → res[res.size - 1]! ≤ nums2[j]!
    -- i is done (nums1 fully consumed)
    invariant "i_done" i = nums1.size
    -- Decreasing: remaining nums2 elements
    decreasing nums2.size - j
  do
    res := res.push nums2[j]!
    j := j + 1
  return res
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

#assert_same_evaluation #[((MergeSortedArrays test1_nums1 test1_nums2).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MergeSortedArrays test2_nums1 test2_nums2).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MergeSortedArrays test3_nums1 test3_nums2).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MergeSortedArrays test4_nums1 test4_nums2).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MergeSortedArrays test5_nums1 test5_nums2).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MergeSortedArrays test6_nums1 test6_nums2).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MergeSortedArrays test7_nums1 test7_nums2).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MergeSortedArrays test8_nums1 test8_nums2).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MergeSortedArrays test9_nums1 test9_nums2).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MergeSortedArrays (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (a : i < nums1.size)
    (invariant_count_pres : ∀ (v : ℤ), Array.count v res = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    : ∀ (v : ℤ), Array.count v res + List.count v [nums1[i]!] = List.count v (List.take (i + OfNat.ofNat 1) nums1.toList) + List.count v (List.take j nums2.toList) := by
    intro v
    rw [invariant_count_pres v]
    have h_len : i < nums1.toList.length := by simp [Array.length_toList]; exact a
    rw [List.take_succ, List.count_append]
    suffices h : List.count v [nums1[i]!] = List.count v (nums1.toList[i]?.toList) by omega
    rw [List.getElem?_eq_getElem h_len, Option.toList_some]
    congr 1
    have h_bound : i < nums1.size := a
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    have h_eq : nums1[i]? = some nums1[i] := Array.getElem?_eq_some_iff.mpr ⟨h_bound, rfl⟩
    rw [h_eq]
    simp

theorem goal_1
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (a_1 : j < nums2.size)
    (invariant_count_pres : ∀ (v : ℤ), Array.count v res = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    : ∀ (v : ℤ), Array.count v res + List.count v [nums2[j]!] = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList) := by
    intro v
    have h_inv := invariant_count_pres v
    have h_j_lt : j < nums2.toList.length := by rwa [Array.length_toList]
    rw [List.take_succ_eq_append_getElem h_j_lt, List.count_append]
    have h_eq : nums2.toList[j] = nums2[j]! := by
      rw [Array.getElem_toList (by exact a_1)]
      simp [Array.getElem!_eq_getD, Array.getD, a_1]
    simp [h_eq]
    omega

theorem goal_2
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (i_2 : ℕ)
    (i_4 : ℕ)
    (res_2 : Array ℤ)
    (if_pos : i_4 < nums1.size)
    (invariant_count_pres2 : ∀ (v : ℤ), Array.count v res_2 = List.count v (List.take i_4 nums1.toList) + List.count v (List.take i_2 nums2.toList))
    : ∀ (v : ℤ), Array.count v res_2 + List.count v [nums1[i_4]!] = List.count v (List.take (i_4 + OfNat.ofNat 1) nums1.toList) + List.count v (List.take i_2 nums2.toList) := by
    intros; expose_names; exact goal_0 nums1 nums2 i_4 i_2 res_2 if_pos invariant_count_pres2 v

theorem goal_3
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : Array ℤ)
    (i_4 : ℕ)
    (res_2 : Array ℤ)
    (invariant_i_bound2 : i_4 ≤ nums1.size)
    (invariant_res_size2 : res_2.size = i_4 + i_2)
    (invariant_res_sorted2 : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_2.size → res_2[i]! ≤ res_2[i + OfNat.ofNat 1]!)
    (if_pos : i_4 < nums1.size)
    (invariant_i_bound : i_1 ≤ nums1.size)
    (invariant_j_bound : i_2 ≤ nums2.size)
    (invariant_res_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_1.size → res_1[i]! ≤ res_1[i + OfNat.ofNat 1]!)
    (invariant_res_size : res_1.size = i_1 + i_2)
    (invariant_count_pres2 : ∀ (v : ℤ), Array.count v res_2 = List.count v (List.take i_4 nums1.toList) + List.count v (List.take i_2 nums2.toList))
    (invariant_last_le_nums1_2 : OfNat.ofNat 0 < res_2.size → i_4 < nums1.size → res_2[res_2.size - OfNat.ofNat 1]! ≤ nums1[i_4]!)
    (invariant_last_le_nums2_2 : OfNat.ofNat 0 < res_2.size → i_2 < nums2.size → res_2[res_2.size - OfNat.ofNat 1]! ≤ nums2[i_2]!)
    (invariant_j_done : i_2 = nums2.size ∨ nums1.size ≤ i_4)
    (done_1 : i_1 < nums1.size → nums2.size ≤ i_2)
    (invariant_last_le_nums1 : OfNat.ofNat 0 < res_1.size → i_1 < nums1.size → res_1[res_1.size - OfNat.ofNat 1]! ≤ nums1[i_1]!)
    (invariant_last_le_nums2 : OfNat.ofNat 0 < res_1.size → i_2 < nums2.size → res_1[res_1.size - OfNat.ofNat 1]! ≤ nums2[i_2]!)
    (invariant_count_pres : ∀ (v : ℤ), Array.count v res_1 = List.count v (List.take i_1 nums1.toList) + List.count v (List.take i_2 nums2.toList))
    : i_4 + OfNat.ofNat 1 < nums1.size → nums1[i_4]! ≤ nums1[i_4 + OfNat.ofNat 1]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_4
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (j_1 : ℕ)
    (res_4 : Array ℤ)
    (if_pos : j_1 < nums2.size)
    (invariant_count_pres3 : ∀ (v : ℤ), Array.count v res_4 = Array.count v nums1 + List.count v (List.take j_1 nums2.toList))
    : ∀ (v : ℤ), Array.count v res_4 + List.count v [nums2[j_1]!] = Array.count v nums1 + List.count v (List.take (j_1 + OfNat.ofNat 1) nums2.toList) := by
    intro v
    rw [invariant_count_pres3 v]
    have h_len : j_1 < nums2.toList.length := by
      rwa [Array.length_toList]
    rw [List.take_succ_eq_append_getElem h_len, List.count_append]
    ring_nf
    congr 1
    simp only [Array.getElem!_eq_getD, Array.getD, dif_pos if_pos, Array.getInternal_eq_getElem, Array.getElem_toList]

theorem goal_5
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : Array ℤ)
    (res_3 : Array ℤ)
    (j_1 : ℕ)
    (res_4 : Array ℤ)
    (invariant_j_bound3 : j_1 ≤ nums2.size)
    (invariant_res_sorted3 : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_4.size → res_4[i]! ≤ res_4[i + OfNat.ofNat 1]!)
    (if_pos : j_1 < nums2.size)
    (invariant_i_bound : i_1 ≤ nums1.size)
    (invariant_j_bound : i_2 ≤ nums2.size)
    (invariant_res_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_1.size → res_1[i]! ≤ res_1[i + OfNat.ofNat 1]!)
    (invariant_res_size : res_1.size = i_1 + i_2)
    (invariant_res_sorted2 : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_3.size → res_3[i]! ≤ res_3[i + OfNat.ofNat 1]!)
    (invariant_res_size3 : res_4.size = nums1.size + j_1)
    (invariant_res_size2 : res_3.size = nums1.size + i_2)
    (invariant_last_le_nums2_3 : OfNat.ofNat 0 < res_4.size → j_1 < nums2.size → res_4[res_4.size - OfNat.ofNat 1]! ≤ nums2[j_1]!)
    (done_1 : i_1 < nums1.size → nums2.size ≤ i_2)
    (invariant_last_le_nums1 : OfNat.ofNat 0 < res_1.size → i_1 < nums1.size → res_1[res_1.size - OfNat.ofNat 1]! ≤ nums1[i_1]!)
    (invariant_last_le_nums2 : OfNat.ofNat 0 < res_1.size → i_2 < nums2.size → res_1[res_1.size - OfNat.ofNat 1]! ≤ nums2[i_2]!)
    (invariant_count_pres : ∀ (v : ℤ), Array.count v res_1 = List.count v (List.take i_1 nums1.toList) + List.count v (List.take i_2 nums2.toList))
    (invariant_last_le_nums2_2 : OfNat.ofNat 0 < res_3.size → i_2 < nums2.size → res_3[res_3.size - OfNat.ofNat 1]! ≤ nums2[i_2]!)
    (invariant_count_pres3 : ∀ (v : ℤ), Array.count v res_4 = Array.count v nums1 + List.count v (List.take j_1 nums2.toList))
    (invariant_count_pres2 : ∀ (v : ℤ), Array.count v res_3 = Array.count v nums1 + List.count v (List.take i_2 nums2.toList))
    : j_1 + OfNat.ofNat 1 < nums2.size → nums2[j_1]! ≤ nums2[j_1 + OfNat.ofNat 1]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_6
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : Array ℤ)
    (res_3 : Array ℤ)
    (i_7 : ℕ)
    (res_5 : Array ℤ)
    (invariant_i_bound : i_1 ≤ nums1.size)
    (invariant_j_bound : i_2 ≤ nums2.size)
    (invariant_res_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_1.size → res_1[i]! ≤ res_1[i + OfNat.ofNat 1]!)
    (invariant_res_size : res_1.size = i_1 + i_2)
    (invariant_res_sorted2 : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_3.size → res_3[i]! ≤ res_3[i + OfNat.ofNat 1]!)
    (invariant_res_size2 : res_3.size = nums1.size + i_2)
    (invariant_j_bound3 : i_7 ≤ nums2.size)
    (invariant_res_sorted3 : ∀ (i : ℕ), i + OfNat.ofNat 1 < res_5.size → res_5[i]! ≤ res_5[i + OfNat.ofNat 1]!)
    (invariant_res_size3 : res_5.size = nums1.size + i_7)
    (done_1 : i_1 < nums1.size → nums2.size ≤ i_2)
    (invariant_last_le_nums1 : OfNat.ofNat 0 < res_1.size → i_1 < nums1.size → res_1[res_1.size - OfNat.ofNat 1]! ≤ nums1[i_1]!)
    (invariant_last_le_nums2 : OfNat.ofNat 0 < res_1.size → i_2 < nums2.size → res_1[res_1.size - OfNat.ofNat 1]! ≤ nums2[i_2]!)
    (invariant_count_pres : ∀ (v : ℤ), Array.count v res_1 = List.count v (List.take i_1 nums1.toList) + List.count v (List.take i_2 nums2.toList))
    (invariant_last_le_nums2_2 : OfNat.ofNat 0 < res_3.size → i_2 < nums2.size → res_3[res_3.size - OfNat.ofNat 1]! ≤ nums2[i_2]!)
    (invariant_count_pres2 : ∀ (v : ℤ), Array.count v res_3 = Array.count v nums1 + List.count v (List.take i_2 nums2.toList))
    (done_3 : nums2.size ≤ i_7)
    (invariant_count_pres3 : ∀ (v : ℤ), Array.count v res_5 = Array.count v nums1 + List.count v (List.take i_7 nums2.toList))
    : postcondition nums1 nums2 res_5 := by
    intros; expose_names; try simp_all; try grind


prove_correct MergeSortedArrays by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums1 nums2 i j res a invariant_count_pres)
  exact (goal_1 nums1 nums2 i j res a_1 invariant_count_pres)
  exact (goal_2 nums1 nums2 i_2 i_4 res_2 if_pos invariant_count_pres2)
  exact (goal_3 nums1 nums2 require_1 i_1 i_2 res_1 i_4 res_2 invariant_i_bound2 invariant_res_size2 invariant_res_sorted2 if_pos invariant_i_bound invariant_j_bound invariant_res_sorted invariant_res_size invariant_count_pres2 invariant_last_le_nums1_2 invariant_last_le_nums2_2 invariant_j_done done_1 invariant_last_le_nums1 invariant_last_le_nums2 invariant_count_pres)
  exact (goal_4 nums1 nums2 j_1 res_4 if_pos invariant_count_pres3)
  exact (goal_5 nums1 nums2 require_1 i_1 i_2 res_1 res_3 j_1 res_4 invariant_j_bound3 invariant_res_sorted3 if_pos invariant_i_bound invariant_j_bound invariant_res_sorted invariant_res_size invariant_res_sorted2 invariant_res_size3 invariant_res_size2 invariant_last_le_nums2_3 done_1 invariant_last_le_nums1 invariant_last_le_nums2 invariant_count_pres invariant_last_le_nums2_2 invariant_count_pres3 invariant_count_pres2)
  exact (goal_6 nums1 nums2 require_1 i_1 i_2 res_1 res_3 i_7 res_5 invariant_i_bound invariant_j_bound invariant_res_sorted invariant_res_size invariant_res_sorted2 invariant_res_size2 invariant_j_bound3 invariant_res_sorted3 invariant_res_size3 done_1 invariant_last_le_nums1 invariant_last_le_nums2 invariant_count_pres invariant_last_le_nums2_2 invariant_count_pres2 done_3 invariant_count_pres3)
end Proof
