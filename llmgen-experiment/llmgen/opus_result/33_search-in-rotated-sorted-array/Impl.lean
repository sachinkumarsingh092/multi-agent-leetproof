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

section Specs
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
method SearchInRotatedSortedArray (nums : List Int) (target : Int)
  return (result : Int)
  require precondition nums target
  ensures postcondition nums target result
  do
  let arr : Array Int := nums.toArray
  let n := arr.size
  if n = 0 then
    return (-1)
  else
    let mut lo : Nat := 0
    let mut hi : Nat := n - 1
    let mut ans : Int := (-1)
    let mut found : Bool := false
    while lo <= hi ∧ ¬found
      invariant "arr_eq" arr = nums.toArray
      invariant "n_eq" n = arr.size
      invariant "n_pos" n > 0
      -- hi is within array bounds
      -- Init: hi = n-1 < n. Pres: hi only decreases or stays.
      invariant "hi_bound" hi < n
      -- if not found, ans is -1
      -- Init: found=false, ans=-1. Pres: ans only changes when found becomes true.
      invariant "not_found_ans" found = false → ans = -1
      -- if found, ans is a valid index of target with uniqueness
      -- Init: found=false so vacuously true.
      -- Pres: when arr[mid]==target, we set ans=mid and found=true.
      invariant "found_correct" found = true →
        (∃ i : Nat, i < nums.length ∧ nums.get? i = some target ∧ ans = Int.ofNat i ∧
          (∀ j : Nat, j < nums.length → nums.get? j = some target → j = i))
      -- if target is in nums and not found, its index lies in [lo, hi]
      -- Init: lo=0, hi=n-1 covers all indices.
      -- Pres: rotated-sorted binary search narrows correctly.
      -- Suff: on exit with found=false, lo > hi means no index → target absent → ans=-1.
      invariant "search_range" found = false →
        (∀ i : Nat, i < nums.length → nums.get? i = some target → lo ≤ i ∧ i ≤ hi)
      done_with postcondition nums target ans
      -- Decreasing: when guard holds (lo ≤ hi ∧ ¬found), measure is hi-lo+1 ≥ 1.
      -- Each iteration either sets found=true (measure → 0) or strictly narrows [lo,hi]
      -- or makes lo > hi (measure → 0). In all cases measure strictly decreases.
      decreasing if lo ≤ hi ∧ ¬found then hi - lo + 1 else 0
    do
      let mid : Nat := lo + (hi - lo) / 2
      if arr[mid]! = target then
        ans := Int.ofNat mid
        found := true
      else
        if arr[lo]! <= arr[mid]! then
          -- left half is sorted
          if arr[lo]! <= target ∧ target < arr[mid]! then
            -- target is in left half
            if mid = 0 then
              break
            else
              hi := mid - 1
          else
            -- target is in right half
            lo := mid + 1
        else
          -- right half is sorted
          if arr[mid]! < target ∧ target <= arr[hi]! then
            -- target is in right half
            lo := mid + 1
          else
            -- target is in left half
            if mid = 0 then
              break
            else
              hi := mid - 1
    return ans
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

#assert_same_evaluation #[((SearchInRotatedSortedArray test1_nums test1_target).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SearchInRotatedSortedArray test2_nums test2_target).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SearchInRotatedSortedArray test3_nums test3_target).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SearchInRotatedSortedArray test4_nums test4_target).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SearchInRotatedSortedArray test5_nums test5_target).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SearchInRotatedSortedArray test6_nums test6_target).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SearchInRotatedSortedArray test7_nums test7_target).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SearchInRotatedSortedArray test8_nums test8_target).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SearchInRotatedSortedArray test9_nums test9_target).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test SearchInRotatedSortedArray (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : List ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (invariant_hi_bound : hi < nums.length)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    : ∃ i < nums.length, nums[i]? = some (nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) ∧ lo.cast + (hi - lo).cast / OfNat.ofNat 2 = i.cast ∧ ∀ j < nums.length, nums[j]? = some (nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) → j = i := by
    set mid := lo + (hi - lo) / 2
    have hnodup := require_1.2.1
    -- mid < nums.length
    have hmid_lt : mid < nums.length := by omega
    -- nums[mid]? = some nums[mid]
    have hmid_eq : nums[mid]? = some nums[mid] := List.getElem?_eq_getElem hmid_lt
    -- getD equals nums[mid]
    have hgetD : (nums[mid]?).getD (OfNat.ofNat 0) = nums[mid] := by
      rw [hmid_eq]; simp
    refine ⟨mid, hmid_lt, ?_, ?_, ?_⟩
    · rw [hgetD]; exact hmid_eq
    · simp [mid]
    · intro j hj hval
      rw [hgetD] at hval
      have hval' : nums[mid]? = nums[j]? := by
        rw [hmid_eq]; exact hval.symm
      exact (List.getElem?_inj hmid_lt hnodup hval').symm

lemma mod_le_of_div_eq_of_le (x y n : ℕ) (hn : 0 < n) (hxy : x ≤ y) (hdiv : x / n = y / n) :
    x % n ≤ y % n := by
  have hx := Nat.div_add_mod x n
  have hy := Nat.div_add_mod y n
  have : n * (x / n) = n * (y / n) := by rw [hdiv]
  omega

-- If x ≤ y and x%n ≤ y%n (with 0 < n), then x/n = y/n
lemma div_eq_of_mod_le_of_le (x y n : ℕ) (hn : 0 < n) (hxy : x ≤ y) (hmod : x % n ≤ y % n) :
    x / n = y / n := by
  by_contra hne
  have hle : x / n ≤ y / n := Nat.div_le_div_right hxy
  have hlt : x / n < y / n := Nat.lt_of_le_of_ne hle hne
  -- y / n ≥ x / n + 1
  -- y = n * (y/n) + y%n ≥ n * (x/n + 1) + 0 = n * (x/n) + n
  -- x = n * (x/n) + x%n < n * (x/n) + n  (since x%n < n)
  -- So x < n*(x/n) + n ≤ y
  -- x%n < n
  have hxmod := Nat.mod_lt x hn
  have hx := Nat.div_add_mod x n
  have hy := Nat.div_add_mod y n
  -- y%n < n
  -- We need x%n > y%n to contradict hmod
  -- x%n = x - n*(x/n)
  -- y%n = y - n*(y/n)
  -- y ≥ n*(x/n+1) = n*(x/n) + n
  have h1 : n * (x / n + 1) ≤ n * (y / n) := Nat.mul_le_mul_left n hlt
  -- n*(x/n+1) = n*(x/n) + n
  have h2 : n * (x / n + 1) = n * (x / n) + n := by ring
  -- y%n = y - n*(y/n)
  -- x%n = x - n*(x/n)
  -- x ≤ y, x/n < y/n
  -- x%n < n
  -- We want to show x%n > y%n
  -- x - n*(x/n) vs y - n*(y/n)
  -- Hmm, this isn't necessarily true. Counter example: x=0, y=10, n=5
  -- x%n = 0, y%n = 0, x/n=0, y/n=2, and 0 ≤ 0 satisfies hmod.
  -- But hlt says 0 < 2, and we want to derive False. But hmod = 0 ≤ 0 is true!
  -- Wait, that violates our hypothesis. Let me re-check.
  -- x=0, y=10, n=5: x%n=0, y%n=0, hmod: 0≤0 true. x/n=0, y/n=2, hne: 0≠2 true.
  -- So we can't prove x/n = y/n from hmod alone when x%n = y%n and there's a multiple of n between them.
  -- The lemma as stated is FALSE.
  sorry


theorem goal_1_0_0
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = ↑i ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target)
    (a_3 : target < nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_2 : lo = OfNat.ofNat 0 → OfNat.ofNat 2 ≤ hi - lo)
    (hf : found = false)
    (i : ℕ)
    (hi_lt : i < nums.length)
    (h_eq : nums[i]? = some target)
    (h_old : lo ≤ i ∧ i ≤ hi)
    (h_lo_le_i : lo ≤ i)
    (h_i_le_hi : i ≤ hi)
    (h_mid : ℕ)
    (h_mid_bound : lo + (hi - lo) / 2 < nums.length)
    (h_lo_bound : lo < nums.length)
    (h_nodup : nums.Nodup)
    : i < lo + (hi - lo) / 2 := by
    sorry

theorem goal_1_0
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = ↑i ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target)
    (a_3 : target < nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_2 : lo = OfNat.ofNat 0 → OfNat.ofNat 2 ≤ hi - lo)
    (hf : found = false)
    (i : ℕ)
    (hi_lt : i < nums.length)
    (h_eq : nums[i]? = some target)
    (h_old : lo ≤ i ∧ i ≤ hi)
    (h_lo_le_i : lo ≤ i)
    (h_i_le_hi : i ≤ hi)
    (h_mid : ℕ)
    (h_mid_bound : lo + (hi - lo) / 2 < nums.length)
    (h_lo_bound : lo < nums.length)
    (h_nodup : nums.Nodup)
    : lo ≤ i ∧ i ≤ lo + (hi - lo) / OfNat.ofNat 2 - OfNat.ofNat 1 := by
    change lo ≤ i ∧ i ≤ lo + (hi - lo) / 2 - 1
    have h_i_lt_mid : i < lo + (hi - lo) / 2 := by expose_names; exact (goal_1_0_0 nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_pos a_2 a_3 if_neg_2 hf i hi_lt h_eq h_old h_lo_le_i h_i_le_hi h_mid h_mid_bound h_lo_bound h_nodup)
    constructor
    · exact h_lo_le_i
    · omega

theorem goal_1
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target)
    (a_3 : target < nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_2 : lo = OfNat.ofNat 0 → OfNat.ofNat 2 ≤ hi - lo)
    : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ lo + (hi - lo) / OfNat.ofNat 2 - OfNat.ofNat 1 := by
    intro hf i hi_lt h_eq
    have h_old := invariant_search_range hf i hi_lt h_eq
    have h_lo_le_i := h_old.1
    have h_i_le_hi := h_old.2
    have h_mid := lo + (hi - lo) / 2
    have h_mid_bound : lo + (hi - lo) / 2 < nums.length := by omega
    have h_lo_bound : lo < nums.length := by omega
    have h_nodup := require_1.2.1
    -- Key: i ≠ mid because nums[i] = target but getD at mid ≠ target
    -- Key: i < mid because of the sorted structure
    -- Combined: i ≤ mid - 1
    -- We prove the combined statement directly
    have h_main : lo ≤ i ∧ i ≤ lo + (hi - lo) / OfNat.ofNat 2 - OfNat.ofNat 1 := by
      expose_names; exact (goal_1_0 nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_pos a_2 a_3 if_neg_2 hf i hi_lt h_eq h_old h_lo_le_i h_i_le_hi h_mid h_mid_bound h_lo_bound h_nodup)
    exact h_main

theorem goal_2
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target)
    : found = false → ∀ i < nums.length, nums[i]? = some target → lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ i ∧ i ≤ hi := by
    sorry



theorem goal_2
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target)
    : found = false → ∀ i < nums.length, nums[i]? = some target → lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ i ∧ i ≤ hi := by
    sorry

theorem goal_3
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_neg_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target)
    (a_3 : target ≤ nums[hi]?.getD (OfNat.ofNat 0))
    : found = false → ∀ i < nums.length, nums[i]? = some target → lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ i ∧ i ≤ hi := by
    sorry

theorem goal_4
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (a : lo ≤ hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (a_1 : found = false)
    (if_neg_1 : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_neg_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0))
    (if_neg_3 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target → nums[hi]?.getD (OfNat.ofNat 0) < target)
    (if_neg_4 : lo = OfNat.ofNat 0 → OfNat.ofNat 2 ≤ hi - lo)
    : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ lo + (hi - lo) / OfNat.ofNat 2 - OfNat.ofNat 1 := by
    sorry

theorem goal_5
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (found : Bool)
    (hi : ℕ)
    (lo : ℕ)
    (invariant_not_found_ans : found = false → ans = -OfNat.ofNat 1)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (if_neg : ¬nums = [])
    (invariant_n_pos : OfNat.ofNat 0 < nums.length)
    (invariant_hi_bound : hi < nums.length)
    (invariant_found_correct : found = true → ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast ∧ ∀ j < nums.length, nums[j]? = some target → j = i)
    (invariant_search_range : found = false → ∀ i < nums.length, nums[i]? = some target → lo ≤ i ∧ i ≤ hi)
    (if_neg_1 : lo ≤ hi → found = true)
    : postcondition nums target ans := by
    sorry



prove_correct SearchInRotatedSortedArray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums hi lo a invariant_hi_bound require_1)
  exact (goal_1 nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_pos a_2 a_3 if_neg_2)
  exact (goal_2 nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_pos if_neg_2)
  exact (goal_3 nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_neg_2 a_2 a_3)
  exact (goal_4 nums target ans found hi lo invariant_not_found_ans a require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range a_1 if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_5 nums target ans found hi lo invariant_not_found_ans require_1 if_neg invariant_n_pos invariant_hi_bound invariant_found_correct invariant_search_range if_neg_1)
end Proof
