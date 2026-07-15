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
def searchHelper (arr : Array Int) (target : Int) (lo hi : Nat) : Int :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if hm : mid < arr.size then
      let midVal := arr[mid]
      if midVal == target then
        Int.ofNat mid
      else if lo < arr.size then
        let loVal := arr[lo]
        if loVal <= midVal then
          -- Left half is sorted
          if loVal <= target && target < midVal then
            searchHelper arr target lo mid
          else
            searchHelper arr target (mid + 1) hi
        else
          -- Right half is sorted
          if midVal < target && target <= arr[hi - 1]! then
            searchHelper arr target (mid + 1) hi
          else
            searchHelper arr target lo mid
      else
        -1
    else
      -1
  else
    -1
termination_by hi - lo

def implementation (nums : List Int) (target : Int) : Int :=
  let arr := nums.toArray
  searchHelper arr target 0 arr.size
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
theorem correctness_goal_0
    (nums : List ℤ)
    (target : ℤ)
    (h_nodup : nums.Nodup)
    (n : ℕ)
    (hn_eq : nums.get? n = some target)
    (hn_lt : n < nums.length)
    : ∀ j < nums.length, nums.get? j = some target → j = n := by
    intro j hj hget
    have hget_n : nums[n] = target := by
      rw [List.get?_eq_getElem?] at hn_eq
      simp [List.getElem?_eq_getElem, hn_lt] at hn_eq
      exact hn_eq
    have hget_j : nums[j] = target := by
      rw [List.get?_eq_getElem?] at hget
      simp [List.getElem?_eq_getElem, hj] at hget
      exact hget
    have : nums[j] = nums[n] := by rw [hget_j, hget_n]
    exact (h_nodup.getElem_inj_iff (hi := hj) (hj := hn_lt)).mp this

private lemma mid_eq_n_of_eq_target
    (nums : List ℤ)
    (target : ℤ)
    (h_nodup : nums.Nodup)
    (n : ℕ)
    (hn_lt : n < nums.length)
    (hn_val : nums.get? n = some target)
    (h_unique : ∀ j < nums.length, nums.get? j = some target → j = n)
    (mid : ℕ)
    (hmid_lt : mid < nums.toArray.size)
    (hmid_eq : nums.toArray[mid] = target) :
    mid = n := by
  have harr_size : nums.toArray.size = nums.length := List.size_toArray
  have hmid_lt_len : mid < nums.length := by omega
  have : nums.get? mid = some target := by
    rw [List.get?_eq_getElem?]
    rw [List.getElem?_eq_some_iff]
    exact ⟨hmid_lt_len, by rw [← List.getElem_toArray hmid_lt]; exact hmid_eq⟩
  exact h_unique mid hmid_lt_len this

private lemma rotated_sorted_left_sorted_range
    (nums : List ℤ)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (lo mid hi n : ℕ)
    (hlo_le_mid : lo ≤ mid)
    (hmid_lt_hi : mid < hi)
    (hhi_le : hi ≤ nums.length)
    (hlo_le_n : lo ≤ n)
    (hn_lt_hi : n < hi)
    (hmid_ne_n : mid ≠ n)
    (hlo_lt_len : lo < nums.length)
    (hmid_lt_len : mid < nums.length)
    (h_left_sorted : nums[lo]'hlo_lt_len ≤ nums[mid]'hmid_lt_len)
    (h_target_in_left : nums[lo]'hlo_lt_len ≤ nums[n]'(by omega) ∧ nums[n]'(by omega) < nums[mid]'hmid_lt_len)
    : n < mid := by
  by_contra h
  push_neg at h
  -- n ≥ mid and n ≠ mid, so n > mid
  have : n > mid := by omega
  -- We need to show contradiction
  -- Actually this doesn't follow purely from the conditions given
  -- We need stronger properties of the rotated sorted array
  sorry

private lemma searchHelper_invariant_left_sorted
    (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hn_lt : n < nums.length)
    (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length)
    (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi)
    (hmid_ne_n : mid ≠ n)
    (hn_getElem : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target)
    (hlo_lt : lo < nums.length)
    (h_left_sorted : nums[lo]'hlo_lt ≤ nums[mid]'(by omega))
    (h_in_left : nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega))
    : lo ≤ n ∧ n < mid := by
  constructor
  · exact hlo_le_n
  · -- We need: n < mid
    -- We know left half [lo, mid] is sorted (since arr[lo] ≤ arr[mid] in a rotated sorted array)
    -- and target is in range [arr[lo], arr[mid])
    -- Since arr[n] = target and arr[lo] ≤ target < arr[mid], we need n in [lo, mid)
    -- Suppose n ≥ mid. Since mid ≠ n, n > mid.
    by_contra h
    push_neg at h
    have hn_gt_mid : n > mid := by omega
    -- The rotation of strict sorted means there exists base strictly sorted with base.IsRotated nums
    obtain ⟨base, hbase_sorted, hbase_nodup, hbase_rot⟩ := h_rot
    -- This is a deep property of rotated sorted arrays
    -- In [lo, mid], elements are strictly increasing because arr[lo] ≤ arr[mid]
    -- means no wrap-around. So arr[lo] < arr[lo+1] < ... < arr[mid].
    -- Since n > mid, arr[n] could be anything relative to arr[mid].
    -- But arr[n] = target < arr[mid] by h_in_left.
    -- If n > mid, then n is in the "other" part of the array.
    -- In a rotated sorted array, elements in [lo, mid] are sorted,
    -- and elements NOT in [lo, mid] but in [lo, hi) are either before the pivot or after.
    -- This requires careful analysis...
    sorry

-- Key helper: in a rotated sorted nodup array, the search helper branch conditions
-- correctly maintain the invariant that n is in [lo, hi)
private lemma rotated_binary_search_branch_invariant
    (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hn_lt : n < nums.length)
    (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length)
    (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi)
    (hmid_ne_n : mid ≠ n)
    (hn_val : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target)
    (hlo_lt : lo < nums.length) :
    -- Left sorted, in left range → n < mid
    (nums[lo]'hlo_lt ≤ nums[mid]'(by omega) →
     (nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega)) →
     n < mid) ∧
    -- Left sorted, not in left range → mid < n
    (nums[lo]'hlo_lt ≤ nums[mid]'(by omega) →
     ¬(nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega)) →
     mid < n) ∧
    -- Right sorted, in right range → mid < n
    (¬(nums[lo]'hlo_lt ≤ nums[mid]'(by omega)) →
     (nums[mid]'(by omega) < target ∧ target ≤ nums[hi - 1]'(by omega)) →
     mid < n) ∧
    -- Right sorted, not in right range → n < mid
    (¬(nums[lo]'hlo_lt ≤ nums[mid]'(by omega)) →
     ¬(nums[mid]'(by omega) < target ∧ target ≤ nums[hi - 1]'(by omega)) →
     n < mid) := by
  obtain ⟨base, hbase_sorted, hbase_nodup, hbase_rot⟩ := h_rot
  -- The rotated sorted structure means that in [lo, hi), there is at most one
  -- "pivot point" where the values wrap around.
  -- Properties:
  -- 1. If nums[lo] ≤ nums[mid], then [lo, mid] is strictly increasing
  -- 2. If nums[lo] > nums[mid], then [mid, hi-1] is strictly increasing
  --
  -- For strictly increasing segments:
  --   value in range ↔ index in range (by strict monotonicity + nodup)
  --
  -- This requires detailed formalization...
  sorry

-- In a rotated sorted array with nodup, 
-- if nums[lo] ≤ nums[mid] with lo ≤ mid, lo < length, mid < length
-- then the segment [lo..mid] is strictly increasing
-- i.e., for lo ≤ i < j ≤ mid, nums[i] < nums[j]
private lemma rotated_sorted_segment_strict_mono
    (nums : List ℤ)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (lo mid : ℕ)
    (hlo_le_mid : lo ≤ mid)
    (hmid_lt : mid < nums.length)
    (h_sorted_seg : nums[lo]'(by omega) ≤ nums[mid]'hmid_lt)
    (i j : ℕ) (hlo_le_i : lo ≤ i) (hi_lt_j : i < j) (hj_le_mid : j ≤ mid) :
    nums[i]'(by omega) < nums[j]'(by omega) := by
  obtain ⟨base, hbase_sorted, _, hbase_rot⟩ := h_rot
  -- base is strictly sorted and base.IsRotated nums
  -- So nums = base.rotate k for some k
  obtain ⟨k, hk⟩ := hbase_rot
  -- Actually List.IsRotated is defined as l ~r l' iff ∃ n, l.rotate n = l'
  -- So base.rotate k = nums... but the direction might be: base ~r nums means ∃ n, base.rotate n = nums
  -- Need to be careful with the API
  -- For now, let's use a different approach
  -- Since nums has nodup, we can use List.Nodup.getElem_inj_iff
  -- Key insight: in a rotated sorted list with nodup and nums[lo] ≤ nums[mid],
  -- the "pivot" (descending point) is NOT in [lo, mid], 
  -- so [lo..mid] is a subarray of a sorted segment.
  -- 
  -- This is hard to formalize without more infrastructure.
  -- Let me try by contradiction using nodup
  sorry

-- A rotated sorted list has at most one descent
-- If nums[i] ≤ nums[j] for i ≤ j, then the segment [i..j] has no descent
-- and is strictly increasing (given nodup)
private lemma rotated_sorted_no_descent_segment
    (nums : List ℤ)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (i j : ℕ)
    (hi_lt : i < nums.length)
    (hj_lt : j < nums.length)
    (hij : i < j)
    (h_le : nums[i]'hi_lt ≤ nums[j]'hj_lt)
    (p : ℕ) (hip : i ≤ p) (hpj : p < j)
    : nums[p]'(by omega) < nums[p+1]'(by omega) := by
  obtain ⟨base, hbase_sorted, _, hbase_rot⟩ := h_rot
  -- base.IsRotated nums means ∃ n, base.rotate n = nums
  obtain ⟨r, hr⟩ := hbase_rot
  -- base.rotate r = nums
  -- base is strictly sorted
  -- In the rotated array, there is at most one descent
  -- (at position (base.length - r - 1) mod base.length)
  -- If nums[i] ≤ nums[j] with i < j, then no descent in [i..j)
  -- So nums[p] < nums[p+1] for all i ≤ p < j
  --
  -- base.get is strictly monotone by hbase_sorted
  -- In the rotated version, the element at position q is base[(q + r) % base.length]
  -- (or base[(q - r) % base.length] depending on rotation direction)
  --
  -- Actually, List.rotate n takes the first n elements and moves them to the back
  -- So (base.rotate r)[q] = base[(q + r) % base.length] when q + r < base.length,
  -- or base[(q + r) - base.length] when q + r ≥ base.length
  -- 
  -- With strict monotonicity of base.get, a descent happens when
  -- (p + r) % len > (p + 1 + r) % len, i.e., when p + r + 1 = len (mod len)
  -- 
  -- If nums[i] ≤ nums[j] means base[(i+r)%len] ≤ base[(j+r)%len]
  -- By strict monotonicity of base, this means (i+r)%len ≤ (j+r)%len
  -- (since base.get is strictly monotone for strictly sorted base)
  --
  -- If (i+r)%len ≤ (j+r)%len, then for all p in [i,j),
  -- (p+r)%len < (p+1+r)%len, so no wrap-around happens in [i,j]
  -- Therefore nums[p] = base[(p+r)%len] < base[(p+1+r)%len] = nums[p+1]
  sorry

-- Helper: (a + b) % n = (a % n + b) % n when b < n
private lemma mod_add_mod_right (a b n : ℕ) (hn : 0 < n) : 
    (a + b) % n = (a % n + b % n) % n := by
  exact Nat.add_mod a b n

private lemma rotated_sorted_segment_incr
    (nums : List ℤ)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (i j : ℕ)
    (hi_lt : i < nums.length)
    (hj_lt : j < nums.length)
    (hij : i ≤ j)
    (h_le : nums[i]'hi_lt ≤ nums[j]'hj_lt)
    (p : ℕ) (hip : i ≤ p) (hpj : p < j)
    : nums[p]'(by omega) < nums[p+1]'(by omega) := by
  obtain ⟨base, hbase_sorted, _, hbase_rot⟩ := h_rot
  obtain ⟨r, hr⟩ := hbase_rot
  have hlen : nums.length = base.length := by rw [← hr, List.length_rotate]
  set len := base.length with hlen_def
  have hlen_pos : 0 < len := by omega
  -- StrictMono on base indices
  have hbase_mono : ∀ (a b : ℕ) (ha : a < len) (hb : b < len), a < b → base[a]'ha < base[b]'hb := by
    intro a b ha hb hab
    exact List.Sorted.get_strictMono hbase_sorted (show (⟨a, by omega⟩ : Fin base.length) < ⟨b, by omega⟩ from hab)
  -- get_eq using subst
  have get_eq : ∀ (k : ℕ) (hk : k < len),
      nums[k]'(by omega) = base[(k + r) % len]'(Nat.mod_lt _ hlen_pos) := by
    intro k hk
    have h1 : nums[k]'(by omega) = (base.rotate r)[k]'(by rw [List.length_rotate]; omega) := by
      congr 1; exact hr.symm
    rw [h1, List.getElem_rotate]
  -- f(i) ≤ f(j) where f(k) = (k + r) % len
  have hfi_le_fj : (i + r) % len ≤ (j + r) % len := by
    by_contra h_neg
    push_neg at h_neg
    have := hbase_mono _ _ (Nat.mod_lt _ hlen_pos) (Nat.mod_lt _ hlen_pos) h_neg
    rw [← get_eq j (by omega), ← get_eq i (by omega)] at this
    omega
  -- Key bound: (i+r)%len + (j-i) < len
  have hji_lt : j - i < len := by omega
  have hsum_bound : (i + r) % len + (j - i) < len := by
    by_contra h_neg
    push_neg at h_neg
    -- (j+r)%len = ((i+r) + (j-i)) % len = ((i+r)%len + (j-i)) % len (modular property)
    have h1 : (j + r) % len = ((i + r) % len + (j - i)) % len := by
      have : j + r = (i + r) + (j - i) := by omega
      conv_lhs => rw [this]
      rw [Nat.add_mod, Nat.mod_eq_of_lt hji_lt]
    -- Since (i+r)%len + (j-i) ∈ [len, 2*len), its mod is (i+r)%len + (j-i) - len
    have h2 : (i + r) % len + (j - i) < 2 * len := by
      have := Nat.mod_lt (i + r) hlen_pos; omega
    have h3 : ((i + r) % len + (j - i)) % len = (i + r) % len + (j - i) - len := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [h3] at h1
    -- So (j+r)%len = (i+r)%len + (j-i) - len < (i+r)%len
    have : (j + r) % len < (i + r) % len := by omega
    omega
  -- (j+r)%len = (i+r)%len + (j-i)
  have key : (j + r) % len = (i + r) % len + (j - i) := by
    have : j + r = (i + r) + (j - i) := by omega
    conv_lhs => rw [this]
    rw [Nat.add_mod, Nat.mod_eq_of_lt hji_lt, Nat.mod_eq_of_lt hsum_bound]
  -- For p in [i, j): similar bounds
  have hp_bound : (i + r) % len + (p - i) < len := by omega
  have hp1_bound : (i + r) % len + (p + 1 - i) < len := by omega
  have hp_eq : (p + r) % len = (i + r) % len + (p - i) := by
    have : p + r = (i + r) + (p - i) := by omega
    conv_lhs => rw [this]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show p - i < len by omega), Nat.mod_eq_of_lt hp_bound]
  have hp1_eq : (p + 1 + r) % len = (i + r) % len + (p + 1 - i) := by
    have : p + 1 + r = (i + r) + (p + 1 - i) := by omega
    conv_lhs => rw [this]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show p + 1 - i < len by omega), Nat.mod_eq_of_lt hp1_bound]
  have hfp_lt : (p + r) % len < (p + 1 + r) % len := by omega
  rw [get_eq p (by omega), get_eq (p + 1) (by omega)]
  exact hbase_mono _ _ (Nat.mod_lt _ hlen_pos) (Nat.mod_lt _ hlen_pos) hfp_lt

-- If segment [i, j] is strictly increasing (no descent), then value ordering = index ordering
-- More precisely: if arr[i] ≤ arr[j] (so segment is sorted), 
-- for any k with i ≤ k ≤ j, arr[k] is determined by position
-- Specifically, for lo ≤ n ≤ j with n ≠ mid and mid < j and lo ≤ mid:
-- if arr[lo] ≤ arr[n] < arr[mid], then lo ≤ n < mid
private lemma sorted_segment_value_implies_index
    (nums : List ℤ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums)
    (lo mid n : ℕ) (hlo_lt : lo < nums.length) (hmid_lt : mid < nums.length) (hn_lt : n < nums.length)
    (hlo_le_mid : lo ≤ mid) (hlo_le_n : lo ≤ n) (hn_le_mid : n ≤ mid)
    (h_sorted : nums[lo]'hlo_lt ≤ nums[mid]'hmid_lt)
    (h_val_ge : nums[lo]'hlo_lt ≤ nums[n]'hn_lt)
    (h_val_lt : nums[n]'hn_lt < nums[mid]'hmid_lt)
    : n < mid := by
  by_contra h
  push_neg at h
  -- n ≤ mid and n ≥ mid, so n = mid
  have : n = mid := by omega
  subst this
  omega -- nums[n] < nums[n] is False

-- Transitivity of strict increasing: if consecutive pairs are strictly increasing,
-- then any two elements with i < j have arr[i] < arr[j]
private lemma strict_increasing_of_consecutive
    (arr : ℕ → ℤ) (lo hi : ℕ) 
    (h_consec : ∀ p, lo ≤ p → p + 1 ≤ hi → arr p < arr (p + 1))
    (i j : ℕ) (hlo_i : lo ≤ i) (hj_hi : j ≤ hi) (hij : i < j)
    : arr i < arr j := by
  induction j with
  | zero => omega
  | succ j' ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with rfl | hij'
    · exact h_consec i hlo_i (by omega)
    · calc arr i < arr j' := ih (by omega) hij'
        _ < arr (j' + 1) := h_consec j' (by omega) (by omega)


theorem correctness_goal_1_0
    (nums : List ℤ)
    (target : ℤ)
    (h_len : nums.length > 0)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hmem : target ∈ nums)
    (n : ℕ)
    (hn_eq : nums.get? n = some target)
    (hn_lt : n < nums.length)
    (hn_val : nums.get? n = some target)
    (h_unique : ∀ j < nums.length, nums.get? j = some target → j = n)
    : ∀ (lo hi : ℕ), lo ≤ n → n < hi → hi ≤ nums.toArray.size → searchHelper nums.toArray target lo hi = Int.ofNat n := by
    sorry

theorem correctness_goal_1
    (nums : List ℤ)
    (target : ℤ)
    (h_len : nums.length > 0)
    (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (hmem : target ∈ nums)
    (n : ℕ)
    (hn_eq : nums.get? n = some target)
    (hn_lt : n < nums.length)
    (hn_val : nums.get? n = some target)
    (h_unique : ∀ j < nums.length, nums.get? j = some target → j = n)
    : searchHelper nums.toArray target 0 nums.toArray.size = Int.ofNat n := by
    have h_general : ∀ lo hi : ℕ, lo ≤ n → n < hi → hi ≤ nums.toArray.size →
      searchHelper nums.toArray target lo hi = Int.ofNat n := by expose_names; exact (correctness_goal_1_0 nums target h_len h_nodup h_rot hmem n hn_eq hn_lt hn_val h_unique)
    exact h_general 0 nums.toArray.size (Nat.zero_le n) (by simp [List.size_toArray]; exact hn_lt) (le_refl _)

theorem correctness_goal_2_0
    (nums : List ℤ)
    (target : ℤ)
    (hmem : target ∉ nums)
    : ∀ (lo hi : ℕ), hi ≤ nums.toArray.size → searchHelper nums.toArray target lo hi = -1 := by
  have hsize : nums.toArray.size = nums.length := List.size_toArray
  suffices h : ∀ n, ∀ lo hi : ℕ, hi - lo = n → hi ≤ nums.toArray.size → searchHelper nums.toArray target lo hi = -1 by
    intro lo hi hhi; exact h _ lo hi rfl hhi
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi hn hhi
    unfold searchHelper
    split
    · rename_i hlt
      dsimp only []
      split
      · rename_i hmid
        have h_ne_arr : ¬(nums.toArray[lo + (hi - lo) / 2] = target) := by
          intro heq
          exact hmem (by rw [← Array.mem_def]; exact Array.mem_of_getElem heq)
        have h_beq_false : (nums.toArray[lo + (hi - lo) / 2] == target) = false :=
          beq_eq_false_iff_ne.mpr h_ne_arr
        simp only [h_beq_false, Bool.false_eq_true, ↓reduceIte]
        split
        · -- lo < arr.size
          split
          · -- loVal <= midVal
            split
            · -- target in left: recurse lo..mid
              exact ih (lo + (hi - lo) / 2 - lo) (by omega) lo (lo + (hi - lo) / 2) (by omega) (by omega)
            · -- target not in left: recurse (mid+1)..hi
              exact ih (hi - (lo + (hi - lo) / 2 + 1)) (by omega) (lo + (hi - lo) / 2 + 1) hi (by omega) hhi
          · split
            · exact ih (hi - (lo + (hi - lo) / 2 + 1)) (by omega) (lo + (hi - lo) / 2 + 1) hi (by omega) hhi
            · exact ih (lo + (hi - lo) / 2 - lo) (by omega) lo (lo + (hi - lo) / 2) (by omega) (by omega)
        · rfl
      · rfl
    · rfl

theorem correctness_goal_2
    (nums : List ℤ)
    (target : ℤ)
    (hmem : target ∉ nums)
    : searchHelper nums.toArray target 0 nums.toArray.size = -1 := by
    have h_general : ∀ lo hi : ℕ, hi ≤ nums.toArray.size → searchHelper nums.toArray target lo hi = -1 := by expose_names; exact (correctness_goal_2_0 nums target hmem)
    exact h_general 0 nums.toArray.size (le_refl _)

theorem correctness_goal
    (nums : List Int)
    (target : Int)
    (h_precond : precondition nums target)
    : postcondition nums target (implementation nums target) := by
    unfold precondition at h_precond
    obtain ⟨h_len, h_nodup, h_rot⟩ := h_precond
    unfold implementation
    by_cases hmem : target ∈ nums
    · -- Target is in nums
      obtain ⟨n, hn_eq⟩ := List.get?_of_mem hmem
      have hn_lt : n < nums.length := by
        rw [List.get?_eq_some_iff] at hn_eq
        exact hn_eq.1
      have hn_val : nums.get? n = some target := by
        rw [List.get?_eq_some_iff]
        rw [List.get?_eq_some_iff] at hn_eq
        exact hn_eq
      have h_unique : ∀ j : Nat, j < nums.length → nums.get? j = some target → j = n := by expose_names; exact (correctness_goal_0 nums target h_nodup n hn_eq hn_lt)
      have h_result : searchHelper nums.toArray target 0 nums.toArray.size = Int.ofNat n := by expose_names; exact (correctness_goal_1 nums target h_len h_nodup h_rot hmem n hn_eq hn_lt hn_val h_unique)
      unfold postcondition
      right
      exact ⟨n, hn_lt, hn_val, h_result, h_unique⟩
    · -- Target is not in nums
      have h_result_neg : searchHelper nums.toArray target 0 nums.toArray.size = -1 := by expose_names; exact (correctness_goal_2 nums target hmem)
      unfold postcondition
      left
      exact ⟨h_result_neg, by unfold inList; exact hmem⟩
end Proof
