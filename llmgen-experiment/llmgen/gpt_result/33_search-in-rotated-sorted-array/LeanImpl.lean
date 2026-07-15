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
    SearchInRotatedSortedArray: return the index of a target value in a possibly rotated strictly-increasing array, or -1 if absent.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. Input is a finite sequence `nums` of integers with distinct values.
    2. There exists an underlying strictly increasing sequence `base` such that `nums` is a cyclic rotation of `base`.
    3. Input also contains an integer `target`.
    4. If `target` occurs in `nums`, the function returns the (0-based) index where it occurs.
    5. Because values are distinct, this index is unique.
    6. If `target` does not occur in `nums`, the function returns -1.
    7. The returned index is always either -1 or a valid index within `nums`.
-/

-- Helper: strict sortedness for lists (ascending with distinctness implied)
def isStrictSorted (nums : List Int) : Prop :=
  nums.Sorted (· < ·)

-- Helper: `nums` is a rotation of some strictly sorted list
-- We require existence of a strictly sorted `base` such that `base.rotate k = nums` for some `k`.
def isRotationOfStrictSorted (nums : List Int) : Prop :=
  ∃ base : List Int,
    isStrictSorted base ∧ base.Nodup ∧ base.IsRotated nums

-- Helper: membership in a list
-- (We keep this as a named predicate to make specs readable.)
def inList (nums : List Int) (x : Int) : Prop :=
  x ∈ nums

-- Precondition: nonempty list, distinct elements, and rotation-of-strict-sorted structure.
def precondition (nums : List Int) (target : Int) : Prop :=
  nums.length > 0 ∧
  nums.Nodup ∧
  isRotationOfStrictSorted nums

-- Postcondition:
-- - If `target` is absent, result is -1.
-- - If `target` is present, result is the unique index (as an `Int`) where it occurs.
def postcondition (nums : List Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ∧ ¬ inList nums target) ∨
  (∃ i : Nat,
    i < nums.length ∧
    nums.get? i = some target ∧
    result = Int.ofNat i ∧
    (∀ j : Nat, j < nums.length → nums.get? j = some target → j = i))
end Specs

section Impl
def implementation (nums : List Int) (target : Int) : Int :=
  let arr : Array Int := nums.toArray
  let n : Nat := arr.size
  -- binary search on [lo, hi) (hi exclusive)
  let rec bs (lo hi : Nat) : Int :=
    if h : lo < hi then
      let mid : Nat := lo + (hi - lo) / 2
      let midVal : Int := arr[mid]!
      if midVal = target then
        Int.ofNat mid
      else
        let loVal : Int := arr[lo]!
        -- Determine which half [lo, mid] or [mid, hi) is sorted, then narrow.
        if loVal ≤ midVal then
          -- Left half [lo, mid] is sorted.
          if loVal ≤ target ∧ target < midVal then
            bs lo mid
          else
            bs (mid + 1) hi
        else
          -- Right half [mid, hi) is sorted.
          let hiVal : Int := arr[hi - 1]!
          if midVal < target ∧ target ≤ hiVal then
            bs (mid + 1) hi
          else
            bs lo mid
    else
      (-1)
  bs 0 n
end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : List Int := [4, 5, 6, 7, 0, 1, 2]
def test1_target : Int := 0
def test1_Expected : Int := 4

-- Test case 2: Example 2
def test2_nums : List Int := [4, 5, 6, 7, 0, 1, 2]
def test2_target : Int := 3
def test2_Expected : Int := (-1)

-- Test case 3: Example 3
def test3_nums : List Int := [1]
def test3_target : Int := 0
def test3_Expected : Int := (-1)

-- Test case 4: Single-element list where target is present
def test4_nums : List Int := [1]
def test4_target : Int := 1
def test4_Expected : Int := 0

-- Test case 5: Unrotated strictly increasing list
def test5_nums : List Int := [0, 1, 2, 3, 4]
def test5_target : Int := 3
def test5_Expected : Int := 3

-- Test case 6: Rotation by 1 (pivot at index 1)
def test6_nums : List Int := [5, 1, 2, 3, 4]
def test6_target : Int := 5
def test6_Expected : Int := 0

-- Test case 7: Target at the last index in a rotated list
def test7_nums : List Int := [3, 4, 5, 1, 2]
def test7_target : Int := 2
def test7_Expected : Int := 4

-- Test case 8: Rotation with negative numbers
def test8_nums : List Int := [0, 1, (-3), (-2), (-1)]
def test8_target : Int := (-2)
def test8_Expected : Int := 3

-- Test case 9: Target absent in an unrotated list
def test9_nums : List Int := [10, 20, 30, 40, 50]
def test9_target : Int := 35
def test9_Expected : Int := (-1)
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums test1_target), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums test2_target), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums test3_target), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums test4_target), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums test5_target), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums test6_target), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums test7_target), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums test8_target), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums test9_target), test9_Expected]
end Assertions

section Pbt
-- Lean wrapper for velvet_plausible_test failed to compile. Giving up on PBT.

-- method implementationPbt (nums : List Int) (target : Int)
--   return (result : Int)
--   require precondition nums target
--   ensures postcondition nums target result
--   do
--   return (implementation nums target)

-- velvet_plausible_test implementationPbt (config := { maxMs := some 5000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (nums : List ℤ)
    (target : ℤ)
    (hmem : inList nums target)
    : ∃ i < nums.length, nums.get? i = some target := by
  -- `inList` is just membership
  dsimp [inList] at hmem
  rcases List.get?_of_mem (l := nums) (a := target) hmem with ⟨i, hi⟩
  -- Extract the bound from `get? i = some target`
  rcases (List.get?_eq_some_iff (l := nums) (n := i) (a := target)).1 hi with ⟨hi_lt, _⟩
  exact ⟨i, hi_lt, hi⟩

theorem correctness_goal_0_1
    (nums : List ℤ)
    (target : ℤ)
    (h_len_pos : nums.length > 0)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hmem : inList nums target)
    (h_exists_idx : ∃ i < nums.length, nums.get? i = some target)
    : ∀ i < nums.length, nums.get? i = some target → implementation nums target = Int.ofNat i := by
    sorry

theorem correctness_goal_0
    (nums : List ℤ)
    (target : ℤ)
    (h_len_pos : nums.length > 0)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hmem : inList nums target)
    : ∃ i < nums.length, nums.get? i = some target ∧ implementation nums target = Int.ofNat i := by
  classical
  have h_exists_idx : ∃ i : Nat, i < nums.length ∧ nums.get? i = some target := by
    expose_names; exact (correctness_goal_0_0 nums target hmem)
  have h_impl_at_idx : ∀ i : Nat, i < nums.length → nums.get? i = some target → implementation nums target = Int.ofNat i := by
    expose_names; exact (correctness_goal_0_1 nums target h_len_pos h_nodup h_rot hmem h_exists_idx)
  rcases h_exists_idx with ⟨i, hi, hget⟩
  refine ⟨i, hi, hget, ?_⟩
  exact h_impl_at_idx i hi hget

theorem correctness_goal_1
    (nums : List ℤ)
    (target : ℤ)
    (h_nodup : nums.Nodup)
    (i : ℕ)
    (hi : i < nums.length)
    (hget : nums.get? i = some target)
    (j : ℕ)
    (hgetj : nums.get? j = some target)
    : i = j := by
    have hI : nums[i]? = some target := by
      simpa [List.get?_eq_getElem?] using hget
    have hJ : nums[j]? = some target := by
      simpa [List.get?_eq_getElem?] using hgetj
    have hEq : nums[i]? = nums[j]? := by
      simpa [hI, hJ]
    exact List.getElem?_inj (xs := nums) (i := i) (j := j) hi h_nodup hEq

theorem correctness_goal_2_0
    (nums : List ℤ)
    (target : ℤ)
    (hne : ¬implementation nums target = -1)
    : ∃ i, implementation nums target = Int.ofNat i := by
  classical

  have bs_range : ∀ (tgt : ℤ) (arr : Array ℤ) (lo hi : Nat),
      implementation.bs tgt arr lo hi = (-1) ∨ ∃ i, implementation.bs tgt arr lo hi = Int.ofNat i := by
    intro tgt arr lo hi
    have aux : ∀ m : Nat, ∀ lo hi : Nat, hi - lo = m →
        implementation.bs tgt arr lo hi = (-1) ∨ ∃ i, implementation.bs tgt arr lo hi = Int.ofNat i := by
      intro m
      refine Nat.strong_induction_on m ?_
      intro m ih lo hi hm

      by_cases hlt : lo < hi
      · set mid : Nat := lo + (hi - lo) / 2 with hmid

        have hlo_le_mid : lo ≤ mid := by
          have : lo ≤ lo + (hi - lo) / 2 := Nat.le_add_right lo ((hi - lo) / 2)
          simpa [hmid] using this

        have hmid_lt_hi : mid < hi := by
          have hpos : 0 < hi - lo := Nat.sub_pos_of_lt hlt
          have hdiv : (hi - lo) / 2 < (hi - lo) := Nat.div_lt_self hpos (by decide)
          have hadd : lo + (hi - lo) / 2 < lo + (hi - lo) := Nat.add_lt_add_left hdiv lo
          have : lo + (hi - lo) / 2 < hi := by
            simpa [Nat.add_sub_of_le (Nat.le_of_lt hlt)] using hadd
          simpa [hmid] using this

        have hdecrLeft : mid - lo < m := by
          have : mid - lo < hi - lo := Nat.sub_lt_sub_right hlo_le_mid hmid_lt_hi
          simpa [hm] using this

        have hdecrRight : hi - (mid + 1) < m := by
          have hlo_lt_mid1 : lo < mid + 1 := Nat.lt_succ_of_le hlo_le_mid
          have : hi - (mid + 1) < hi - lo := Nat.sub_lt_sub_left hlt hlo_lt_mid1
          simpa [hm] using this

        by_cases hEq : arr[mid]! = tgt
        · right
          refine ⟨mid, ?_⟩
          unfold implementation.bs
          simp [hlt, ← hmid, hEq]

        · by_cases hLeftSorted : arr[lo]! ≤ arr[mid]!
          · by_cases hTargetInLeft : arr[lo]! ≤ tgt ∧ tgt < arr[mid]!
            · have ihLeft := ih (mid - lo) hdecrLeft lo mid rfl
              unfold implementation.bs
              simp [hlt, ← hmid, hEq, hLeftSorted, hTargetInLeft]
              exact ihLeft
            · have ihRight := ih (hi - (mid + 1)) hdecrRight (mid + 1) hi rfl
              unfold implementation.bs
              simp [hlt, ← hmid, hEq, hLeftSorted, hTargetInLeft]
              exact ihRight
          · by_cases hTargetInRight : arr[mid]! < tgt ∧ tgt ≤ arr[hi - 1]!
            · have ihRight := ih (hi - (mid + 1)) hdecrRight (mid + 1) hi rfl
              unfold implementation.bs
              simp [hlt, ← hmid, hEq, hLeftSorted, hTargetInRight]
              exact ihRight
            · have ihLeft := ih (mid - lo) hdecrLeft lo mid rfl
              unfold implementation.bs
              simp [hlt, ← hmid, hEq, hLeftSorted, hTargetInRight]
              exact ihLeft

      · left
        unfold implementation.bs
        simp [hlt]

    exact aux (hi - lo) lo hi rfl

  have hrange : implementation nums target = (-1) ∨ ∃ i, implementation nums target = Int.ofNat i := by
    simpa [implementation] using (bs_range target (nums.toArray) 0 (nums.toArray).size)

  rcases hrange with hneg | hpos
  · exfalso
    exact hne hneg
  · exact hpos

theorem correctness_goal_2_1
    (nums : List ℤ)
    (target : ℤ)
    (h_len_pos : nums.length > 0)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hmem : ¬inList nums target)
    (hne : ¬implementation nums target = -1)
    (i : ℕ)
    (hi : implementation nums target = Int.ofNat i)
    : inList nums target := by
    sorry

theorem correctness_goal_2
    (nums : List ℤ)
    (target : ℤ)
    (h_len_pos : nums.length > 0)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hmem : ¬inList nums target)
    : implementation nums target = -1 := by
  classical
  by_contra hne
  have h_nonneg_form : (∃ i : Nat, implementation nums target = Int.ofNat i) := by
    expose_names; exact (correctness_goal_2_0 nums target hne)
  rcases h_nonneg_form with ⟨i, hi⟩
  have h_found_mem : inList nums target := by
    expose_names; exact (correctness_goal_2_1 nums target h_len_pos h_nodup h_rot hmem hne i hi)
  exact hmem h_found_mem

theorem correctness_goal
    (nums : List Int)
    (target : Int)
    (h_precond : precondition nums target)
    : postcondition nums target (implementation nums target) := by
  classical
  rcases h_precond with ⟨h_len_pos, h_nodup, h_rot⟩
  by_cases hmem : inList nums target
  · -- target present
    have h_impl_present : ∃ i : Nat,
        i < nums.length ∧
        nums.get? i = some target ∧
        implementation nums target = Int.ofNat i := by
      expose_names; exact (correctness_goal_0 nums target h_len_pos h_nodup h_rot hmem)
    rcases h_impl_present with ⟨i, hi, hget, himpl⟩
    refine Or.inr ?_
    refine ⟨i, hi, hget, himpl, ?_⟩
    intro j hj hgetj
    -- uniqueness from Nodup
    have hi' : i < nums.length := hi
    have hj' : j < nums.length := hj
    -- convert get? equalities to getElem equalities and use Nodup
    have h_eq : i = j := by
      expose_names; exact (correctness_goal_1 nums target h_nodup i hi hget j hgetj)
    simpa [h_eq]
  · -- target absent
    have h_impl_absent : implementation nums target = (-1) := by
      expose_names; exact (correctness_goal_2 nums target h_len_pos h_nodup h_rot hmem)
    refine Or.inl ?_
    refine ⟨h_impl_absent, ?_⟩
    simpa [inList] using hmem
end Proof
