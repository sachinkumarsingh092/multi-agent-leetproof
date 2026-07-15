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

section Specs
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
method SortAnArray (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  let offset : Int := 50000
  let rangeSize : Nat := 100001
  -- Step 1: Build count array
  let mut counts := Array.replicate rangeSize (0 : Int)
  let mut i := 0
  while i < nums.size
    -- counts array size is preserved through set!
    invariant "counts_size_1" counts.size = rangeSize
    -- loop counter bounded
    invariant "i_bound" 0 ≤ i ∧ i ≤ nums.size
    -- counts tracks frequency of each value in nums[0..i]
    -- Init: extract nums 0 0 is empty, count is 0, counts is all zeros. ✓
    -- Pres: setting counts[idx] += 1 reflects adding nums[i] to the prefix. ✓
    -- Suff: at exit i = nums.size, so extract nums 0 nums.size = nums. ✓
    invariant "counts_freq" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal →
      counts[(v + offset).toNat]! = (Array.extract nums 0 i).count v
    decreasing nums.size - i
  do
    let v := nums[i]!
    let idx := (v + offset).toNat
    counts := counts.set! idx (counts[idx]! + 1)
    i := i + 1
  -- Step 2: Build result from counts
  let mut result := Array.mkEmpty nums.size
  let mut j := 0
  while j < rangeSize
    -- counts size preserved (counts is not mutated in this loop)
    invariant "counts_size_2" counts.size = rangeSize
    -- outer loop counter bounded
    invariant "j_bound" 0 ≤ j ∧ j ≤ rangeSize
    -- result is sorted in nondecreasing order
    -- Init: empty array is sorted. ✓
    -- Pres: inner loop only pushes j-offset which is ≥ all existing elements. ✓
    invariant "result_sorted" isSortedNondecreasing result
    -- all result elements are within allowed range
    -- Init: empty array trivially satisfies. ✓
    -- Pres: j ranges 0..100000, so j-offset ranges -50000..50000 = [minVal,maxVal]. ✓
    invariant "result_in_range" allInRange result
    -- counts still reflects original frequencies from nums
    invariant "counts_is_freq" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal →
      counts[(v + offset).toNat]! = nums.count v
    -- values already fully processed have correct count in result
    -- Init: j=0, no v has (v+offset).toNat < 0, vacuously true. ✓
    -- Pres: after inner loop, current j's value is fully pushed. ✓
    -- Suff: at j=rangeSize, all valid v are covered → ∀v, result.count v = nums.count v. ✓
    invariant "result_count_done" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal → (v + offset).toNat < j →
      result.count v = nums.count v
    -- values not yet processed have zero count in result
    -- Init: j=0, result empty, all counts are 0. ✓
    -- Pres: inner loop only pushes j-offset; values with index > j untouched. ✓
    invariant "result_count_pending" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal → (v + offset).toNat ≥ j →
      result.count v = 0
    -- all elements currently in result are ≤ the last processed value
    -- This + sorted ensures pushing j-offset maintains sortedness
    invariant "result_upper" ∀ (k : Nat), k < result.size → result[k]! ≤ (↑j : Int) - offset
    decreasing rangeSize - j
  do
    let mut c := counts[j]!
    while c > 0
      -- c is non-negative (Int, starts at counts[j]!, decremented toward 0)
      invariant "c_nonneg" 0 ≤ c
      -- result remains sorted after each push
      invariant "inner_sorted" isSortedNondecreasing result
      -- result elements remain in range
      invariant "inner_in_range" allInRange result
      -- all result elements are ≤ current value j - offset (for sortedness)
      invariant "inner_upper" ∀ (k : Nat), k < result.size → result[k]! ≤ (↑j : Int) - offset
      -- j and counts unchanged through inner loop
      invariant "inner_j_bound" 0 ≤ j ∧ j < rangeSize
      invariant "inner_counts_size" counts.size = rangeSize
      -- counts still reflects original frequencies
      invariant "inner_counts_freq" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal →
        counts[(v + offset).toNat]! = nums.count v
      -- values before j are fully accounted for in result
      invariant "inner_done" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal → (v + offset).toNat < j →
        result.count v = nums.count v
      -- values after j have zero count in result
      invariant "inner_pending" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal → (v + offset).toNat > j →
        result.count v = 0
      -- partial progress: for current value j-offset, we've pushed (counts[j]! - c) copies
      -- Init: c = counts[j]!, so counts[j]! - c = 0, result.count v = 0 from outer inv. ✓
      -- Pres: push increases count by 1, c decreases by 1. ✓
      -- Suff: c=0 → result.count v = counts[j]! = nums.count v. ✓
      invariant "inner_partial" ∀ (v : Int), minVal ≤ v ∧ v ≤ maxVal → (v + offset).toNat = j →
        result.count v = (counts[j]! - c).toNat
      decreasing c.toNat
    do
      result := result.push (j - offset)
      c := c - 1
    j := j + 1
  return result
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

#assert_same_evaluation #[((SortAnArray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SortAnArray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SortAnArray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SortAnArray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SortAnArray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SortAnArray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SortAnArray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SortAnArray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SortAnArray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test SortAnArray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0_0
    (nums : Array ℤ)
    (i : ℕ)
    (h_nums_range : -50000 ≤ nums[i]! ∧ nums[i]! ≤ 50000)
    (v : ℤ)
    (hv_lo : -OfNat.ofNat 50000 ≤ v)
    (heq : ¬nums[i]! = v)
    : (nums[i]! + OfNat.ofNat 50000).toNat ≠ (v + OfNat.ofNat 50000).toNat := by
    intro h
    apply heq
    have h1 : (0 : ℤ) ≤ nums[i]! + 50000 := by omega
    have h2 : (0 : ℤ) ≤ v + 50000 := by omega
    have h3 : ((nums[i]! + 50000).toNat : ℤ) = nums[i]! + 50000 := Int.toNat_of_nonneg h1
    have h4 : ((v + 50000).toNat : ℤ) = v + 50000 := Int.toNat_of_nonneg h2
    have h5 : (nums[i]! + 50000).toNat = (v + 50000).toNat := h
    have h6 : ((nums[i]! + 50000).toNat : ℤ) = ((v + 50000).toNat : ℤ) := by exact_mod_cast h5
    linarith

theorem goal_0_1
    (nums : Array ℤ)
    (counts : Array ℤ)
    (i : ℕ)
    (v : ℤ)
    (h_diff_idx : (nums[i]! + OfNat.ofNat 50000).toNat ≠ (v + OfNat.ofNat 50000).toNat)
    : (counts.setIfInBounds (nums[i]! + OfNat.ofNat 50000).toNat
      (counts[(nums[i]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1))[(v + OfNat.ofNat 50000).toNat]! =
  counts[(v + OfNat.ofNat 50000).toNat]! := by
    show (counts.setIfInBounds (nums[i]! + OfNat.ofNat 50000).toNat
      (counts[(nums[i]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1)).getD ((v + OfNat.ofNat 50000).toNat) default =
      counts.getD ((v + OfNat.ofNat 50000).toNat) default
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h_diff_idx]

theorem goal_0
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (counts : Array ℤ)
    (i : ℕ)
    (invariant_counts_size_1 : counts.size = OfNat.ofNat 100001)
    (a_1 : i ≤ nums.size)
    (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → counts[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i)).cast)
    (if_pos : i < nums.size)
    (a : True)
    : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (counts.setIfInBounds (nums[i]! + OfNat.ofNat 50000).toNat (counts[(nums[i]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1))[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))).cast := by
    have h_extract : nums.extract 0 (i + 1) = (nums.extract 0 i).push (nums[i]!) := by expose_names; intros; expose_names; try simp_all; try grind
    have h_nums_range : -(50000 : ℤ) ≤ nums[i]! ∧ nums[i]! ≤ 50000 := require_1 i if_pos
    intro v hv_lo hv_hi
    rw [h_extract, Array.count_push]
    by_cases heq : nums[i]! = v
    · -- Same value
      subst heq
      simp only [beq_self_eq_true, ite_true]
      have h_getelem_eq : (counts.setIfInBounds (nums[i]! + OfNat.ofNat 50000).toNat (counts[(nums[i]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1))[(nums[i]! + OfNat.ofNat 50000).toNat]! = counts[(nums[i]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1 := by expose_names; intros; expose_names; try ( simp at * ); try grind
      rw [h_getelem_eq, invariant_counts_freq _ hv_lo hv_hi]
      push_cast; ring
    · -- Different value
      have h_diff_idx : (nums[i]! + OfNat.ofNat 50000).toNat ≠ (v + OfNat.ofNat 50000).toNat := by expose_names; exact (goal_0_0 nums i h_nums_range v hv_lo heq)
      have h_getelem_ne : (counts.setIfInBounds (nums[i]! + OfNat.ofNat 50000).toNat (counts[(nums[i]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1))[(v + OfNat.ofNat 50000).toNat]! = counts[(v + OfNat.ofNat 50000).toNat]! := by expose_names; exact (goal_0_1 nums counts i v h_diff_idx)
      rw [h_getelem_ne, invariant_counts_freq v hv_lo hv_hi]
      have h_beq_false : (nums[i]! == v) = false := by
        simp [beq_iff_eq]; exact heq
      simp [h_beq_false]

theorem goal_1 : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (Array.replicate (OfNat.ofNat 100001) (OfNat.ofNat 0))[(v + OfNat.ofNat 50000).toNat]! = OfNat.ofNat 0 := by
    intro v hv_lo hv_hi
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, Array.size_replicate]
    split
    · simp
    · simp

theorem goal_2
    (j : ℕ)
    (result_1 : Array ℤ)
    (invariant_inner_sorted : ∀ (i j : ℕ), i < j → j < result_1.size → result_1[i]! ≤ result_1[j]!)
    (invariant_inner_upper : ∀ k < result_1.size, result_1[k]! ≤ j.cast - OfNat.ofNat 50000)
    : ∀ (i j_1 : ℕ), i < j_1 → j_1 < result_1.size + OfNat.ofNat 1 → (result_1.push (j.cast - OfNat.ofNat 50000))[i]! ≤ (result_1.push (j.cast - OfNat.ofNat 50000))[j_1]! := by
    intro i' j_1 hij hj1
    change j_1 < result_1.size + 1 at hj1
    set val := (j : ℤ) - OfNat.ofNat 50000 with val_def
    -- Key lemma: for k < result_1.size, (result_1.push val)[k]! = result_1[k]!
    have push_lt : ∀ k, k < result_1.size → (result_1.push val)[k]! = result_1[k]! := by
      intro k hk
      show (result_1.push val).getD k default = result_1.getD k default
      simp [Array.getD, Array.size_push, hk, show k < result_1.size + 1 from by omega,
            Array.getElem_push_lt hk]
    -- Key lemma: (result_1.push val)[result_1.size]! = val
    have push_eq : (result_1.push val)[result_1.size]! = val := by
      show (result_1.push val).getD result_1.size default = val
      simp [Array.getD, Array.size_push, Array.getElem_push, Nat.lt_irrefl]
    by_cases hj1_lt : j_1 < result_1.size
    · have hi_lt : i' < result_1.size := by omega
      rw [push_lt i' hi_lt, push_lt j_1 hj1_lt]
      exact invariant_inner_sorted i' j_1 hij hj1_lt
    · have hj1_eq : j_1 = result_1.size := by omega
      subst hj1_eq
      have hi_lt : i' < result_1.size := by omega
      rw [push_lt i' hi_lt, push_eq]
      exact invariant_inner_upper i' hi_lt

theorem goal_3
    (j : ℕ)
    (if_pos : j < OfNat.ofNat 100001)
    (result_1 : Array ℤ)
    (invariant_inner_in_range : ∀ i < result_1.size, -OfNat.ofNat 50000 ≤ result_1[i]! ∧ result_1[i]! ≤ OfNat.ofNat 50000)
    (a_5 : j < OfNat.ofNat 100001)
    : ∀ i < result_1.size + OfNat.ofNat 1, -OfNat.ofNat 50000 ≤ (result_1.push (j.cast - OfNat.ofNat 50000))[i]! ∧ (result_1.push (j.cast - OfNat.ofNat 50000))[i]! ≤ OfNat.ofNat 50000 := by
    intro i hi
    have hi' : i < result_1.size + 1 := hi
    have hib : i < (result_1.push (j.cast - OfNat.ofNat 50000)).size := by
      rw [Array.size_push]; exact hi'
    -- Convert [i]! to [i] using the in-bounds proof
    have hconv : (result_1.push (j.cast - OfNat.ofNat 50000))[i]! =
        (result_1.push (j.cast - OfNat.ofNat 50000))[i]'hib := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?, Array.getElem?_eq_getElem hib]
    rw [hconv, Array.getElem_push]
    split
    · -- i < result_1.size: old element
      rename_i h
      have hconv2 : result_1[i]'h = result_1[i]! := by
        simp [Array.getElem!_eq_getD, Array.getD_getElem?, Array.getElem?_eq_getElem h]
      rw [hconv2]
      exact invariant_inner_in_range i h
    · -- i ≥ result_1.size: pushed element
      have hj_nonneg : (j : ℤ) ≥ 0 := Int.ofNat_nonneg j
      have hj_lt : (j : ℤ) < 100001 := by exact_mod_cast a_5
      constructor <;> linarith

theorem goal_4
    (j : ℕ)
    (result_1 : Array ℤ)
    (invariant_inner_upper : ∀ k < result_1.size, result_1[k]! ≤ j.cast - OfNat.ofNat 50000)
    : ∀ k < result_1.size + OfNat.ofNat 1, (result_1.push (j.cast - OfNat.ofNat 50000))[k]! ≤ j.cast - OfNat.ofNat 50000 := by
    intro k hk
    by_cases h : k < result_1.size
    · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt h,
                  Option.getD_some]
      have := invariant_inner_upper k h
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                  Array.getElem?_eq_getElem h, Option.getD_some] at this
      exact this
    · have hk_eq : k = result_1.size := by
        have : k < result_1.size + 1 := hk
        omega
      subst hk_eq
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push_eq,
                  Option.getD_some]
      exact le_refl _

theorem goal_5
        (nums : Array ℤ)
        (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
        (i_1 : Array ℤ)
        (i_2 : ℕ)
        (j : ℕ)
        (result : Array ℤ)
        (invariant_counts_size_2 : i_1.size = OfNat.ofNat 100001)
        (a_3 : j ≤ OfNat.ofNat 100001)
        (invariant_result_sorted : ∀ (i j : ℕ), i < j → j < result.size → result[i]! ≤ result[j]!)
        (invariant_result_in_range : ∀ i < result.size, -OfNat.ofNat 50000 ≤ result[i]! ∧ result[i]! ≤ OfNat.ofNat 50000)
        (invariant_counts_is_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast)
        (invariant_result_count_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < j → Array.count v result = Array.count v nums)
        (invariant_result_upper : ∀ k < result.size, result[k]! ≤ j.cast - OfNat.ofNat 50000)
        (if_pos : j < OfNat.ofNat 100001)
        (c : ℤ)
        (result_1 : Array ℤ)
        (invariant_c_nonneg : OfNat.ofNat 0 ≤ c)
        (invariant_inner_sorted : ∀ (i j : ℕ), i < j → j < result_1.size → result_1[i]! ≤ result_1[j]!)
        (invariant_inner_in_range : ∀ i < result_1.size, -OfNat.ofNat 50000 ≤ result_1[i]! ∧ result_1[i]! ≤ OfNat.ofNat 50000)
        (invariant_inner_upper : ∀ k < result_1.size, result_1[k]! ≤ j.cast - OfNat.ofNat 50000)
        (a_5 : j < OfNat.ofNat 100001)
        (invariant_inner_counts_size : i_1.size = OfNat.ofNat 100001)
        (invariant_inner_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast)
        (invariant_inner_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < j → Array.count v result_1 = Array.count v nums)
        (invariant_inner_partial : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat = j → Array.count v result_1 = (i_1[j]! - c).toNat)
        (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001)
        (a_1 : i_2 ≤ nums.size)
        (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast)
        (a_2 : True)
        (invariant_result_count_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → j ≤ (v + OfNat.ofNat 50000).toNat → Array.count v result = OfNat.ofNat 0)
        (a_4 : True)
        (invariant_inner_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → j.cast < v + OfNat.ofNat 50000 → Array.count v result_1 = OfNat.ofNat 0)
        (if_pos_1 : OfNat.ofNat 0 < c)
        (a : True)
        (done_1 : nums.size ≤ i_2)
        : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat = j → Array.count v (result_1.push (j.cast - OfNat.ofNat 50000)) = (i_1[j]! - (c - OfNat.ofNat 1)).toNat := by
        sorry

theorem goal_6
        (nums : Array ℤ)
        (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
        (i_1 : Array ℤ)
        (i_2 : ℕ)
        (j : ℕ)
        (result : Array ℤ)
        (invariant_counts_size_2 : i_1.size = OfNat.ofNat 100001)
        (a_3 : j ≤ OfNat.ofNat 100001)
        (invariant_result_sorted : ∀ (i j : ℕ), i < j → j < result.size → result[i]! ≤ result[j]!)
        (invariant_result_in_range : ∀ i < result.size, -OfNat.ofNat 50000 ≤ result[i]! ∧ result[i]! ≤ OfNat.ofNat 50000)
        (invariant_counts_is_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast)
        (invariant_result_count_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < j → Array.count v result = Array.count v nums)
        (invariant_result_upper : ∀ k < result.size, result[k]! ≤ j.cast - OfNat.ofNat 50000)
        (if_pos : j < OfNat.ofNat 100001)
        (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001)
        (a_1 : i_2 ≤ nums.size)
        (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast)
        (a_2 : True)
        (invariant_result_count_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → j ≤ (v + OfNat.ofNat 50000).toNat → Array.count v result = OfNat.ofNat 0)
        (a : True)
        (done_1 : nums.size ≤ i_2)
        : OfNat.ofNat 0 ≤ i_1[j]! := by
        sorry

theorem goal_7
        (nums : Array ℤ)
        (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
        (i_1 : Array ℤ)
        (i_2 : ℕ)
        (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001)
        (a_1 : i_2 ≤ nums.size)
        (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast)
        (a : True)
        (done_1 : nums.size ≤ i_2)
        : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast := by
        sorry


theorem goal_8
        (nums : Array ℤ)
        (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
        (i_1 : Array ℤ)
        (i_2 : ℕ)
        (invariant_counts_size_2 : i_1.size = OfNat.ofNat 100001)
        (invariant_counts_is_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v nums).cast)
        (i_4 : ℕ)
        (result_1 : Array ℤ)
        (invariant_counts_size_1 : i_1.size = OfNat.ofNat 100001)
        (a_1 : i_2 ≤ nums.size)
        (invariant_counts_freq : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = (Array.count v (nums.extract (OfNat.ofNat 0) i_2)).cast)
        (a_3 : i_4 ≤ OfNat.ofNat 100001)
        (invariant_result_sorted : ∀ (i j : ℕ), i < j → j < result_1.size → result_1[i]! ≤ result_1[j]!)
        (invariant_result_in_range : ∀ i < result_1.size, -OfNat.ofNat 50000 ≤ result_1[i]! ∧ result_1[i]! ≤ OfNat.ofNat 50000)
        (invariant_result_count_done : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (v + OfNat.ofNat 50000).toNat < i_4 → Array.count v result_1 = Array.count v nums)
        (invariant_result_upper : ∀ k < result_1.size, result_1[k]! ≤ i_4.cast - OfNat.ofNat 50000)
        (a : True)
        (done_1 : nums.size ≤ i_2)
        (a_2 : True)
        (done_2 : OfNat.ofNat 100001 ≤ i_4)
        (invariant_result_count_pending : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_4 ≤ (v + OfNat.ofNat 50000).toNat → Array.count v result_1 = OfNat.ofNat 0)
        : postcondition nums result_1 := by
        sorry

prove_correct SortAnArray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at * <;> expose_names); try (conv => congr <;> simp) ; try rfl; try expose_names)
  exact (goal_0 nums require_1 counts i invariant_counts_size_1 a_1 invariant_counts_freq if_pos a)
  exact (goal_1)
  exact (goal_2 j result_1 invariant_inner_sorted invariant_inner_upper)
  exact (goal_3 j if_pos result_1 invariant_inner_in_range a_5)
  exact (goal_4 j result_1 invariant_inner_upper)
  exact (goal_5 nums require_1 i_1 i_2 j result invariant_counts_size_2 a_3 invariant_result_sorted invariant_result_in_range invariant_counts_is_freq invariant_result_count_done invariant_result_upper if_pos c result_1 invariant_c_nonneg invariant_inner_sorted invariant_inner_in_range invariant_inner_upper a_5 invariant_inner_counts_size invariant_inner_counts_freq invariant_inner_done invariant_inner_partial invariant_counts_size_1 a_1 invariant_counts_freq a_2 invariant_result_count_pending a_4 invariant_inner_pending if_pos_1 a done_1)
  exact (goal_6 nums require_1 i_1 i_2 j result invariant_counts_size_2 a_3 invariant_result_sorted invariant_result_in_range invariant_counts_is_freq invariant_result_count_done invariant_result_upper if_pos invariant_counts_size_1 a_1 invariant_counts_freq a_2 invariant_result_count_pending a done_1)
  exact (goal_7 nums require_1 i_1 i_2 invariant_counts_size_1 a_1 invariant_counts_freq a done_1)
  exact (goal_8 nums require_1 i_1 i_2 invariant_counts_size_2 invariant_counts_is_freq i_4 result_1 invariant_counts_size_1 a_1 invariant_counts_freq a_3 invariant_result_sorted invariant_result_in_range invariant_result_count_done invariant_result_upper a done_1 a_2 done_2 invariant_result_count_pending)
end Proof
