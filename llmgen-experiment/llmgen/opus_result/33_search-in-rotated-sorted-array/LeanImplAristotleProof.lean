import Lean

import Mathlib

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
    nums[i]? = some target ∧
    result = Int.ofNat i ∧
    (∀ j : Nat, j < nums.length → nums[j]? = some target → j = i))
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

section Proof

/-
PROBLEM
Helper: strictly sorted base list gives strict monotonicity on base indices

PROVIDED SOLUTION
isStrictSorted base means base.Sorted (· < ·), which is List.Pairwise (· < ·). Use List.pairwise_iff_getElem or similar to extract the element-wise comparison for i < j.
-/
lemma sorted_base_strict_lt (base : List ℤ) (h_sorted : isStrictSorted base)
    (i j : ℕ) (hi : i < base.length) (hj : j < base.length) (hij : i < j) :
    base[i] < base[j] := by
  -- Since `base` is strictly sorted, we have `base[i] < base[j]` for `i < j` by definition of `isStrictSorted`.
  have h_pairwise : List.Pairwise (· < ·) base := by
    exact h_sorted;
  exact List.pairwise_iff_get.mp h_pairwise _ _ hij

/-
PROBLEM
Helper: in a rotation of a sorted list, if we know the base indices are ordered,
we get the corresponding values are ordered

PROVIDED SOLUTION
Since base.rotate k = nums, by List.getElem_rotate we have nums[i] = base[(i+k) % base.length] and nums[j] = base[(j+k) % base.length]. Since (i+k) % base.length < (j+k) % base.length and base is strictly sorted, we get base[(i+k)%L] < base[(j+k)%L] by sorted_base_strict_lt, hence nums[i] < nums[j].

Use: rw [← h_eq], then simp [List.getElem_rotate], then apply sorted_base_strict_lt.
-/
lemma rotation_preserves_order (base : List ℤ) (k : ℕ) (h_sorted : isStrictSorted base)
    (nums : List ℤ) (h_eq : base.rotate k = nums)
    (i j : ℕ) (hi : i < nums.length) (hj : j < nums.length) (hij : i < j)
    (h_no_wrap : (i + k) % base.length < (j + k) % base.length) :
    nums[i] < nums[j] := by
  convert sorted_base_strict_lt base h_sorted _ _ _ _ _ using 1;
  convert List.getElem_rotate _ _ _ _ using 1;
  convert rfl;
  exact h_eq;
  rotate_left;
  convert List.getElem_rotate _ _ _ _ using 1;
  convert rfl;
  exact h_eq;
  · aesop;
  · assumption;
  · aesop

/-
PROBLEM
Helper: if nums[lo] ≤ nums[mid] in a rotation, then the base indices don't wrap
(i.e., (lo+k)%L ≤ (mid+k)%L)

PROVIDED SOLUTION
By contradiction. If (lo+k)%L > (mid+k)%L, then base[(lo+k)%L] > base[(mid+k)%L] (since base is strictly sorted and the base index of lo is larger). But nums[lo] = base[(lo+k)%L] and nums[mid] = base[(mid+k)%L], so nums[lo] > nums[mid], contradicting h_le.

For the equality case: if (lo+k)%L = (mid+k)%L, then since lo ≤ mid and both are < L (= nums.length = base.length), we must have lo = mid. So (lo+k)%L ≤ (mid+k)%L trivially.

More precisely: use List.getElem_rotate to rewrite nums[lo] and nums[mid] in terms of base, then use sorted_base_strict_lt to derive the contradiction.
-/
lemma rotation_no_wrap_of_le (base : List ℤ) (k : ℕ) (h_sorted : isStrictSorted base)
    (h_nodup : base.Nodup)
    (nums : List ℤ) (h_eq : base.rotate k = nums)
    (lo mid : ℕ) (hlo : lo < nums.length) (hmid : mid < nums.length) (hlo_le_mid : lo ≤ mid)
    (h_le : nums[lo] ≤ nums[mid]) :
    (lo + k) % base.length ≤ (mid + k) % base.length := by
  contrapose! h_le;
  simp_all +decide [ ← h_eq, List.getElem_rotate ];
  apply sorted_base_strict_lt base h_sorted;
  assumption

/-
PROBLEM
Helper: if (lo+k)%L ≤ (mid+k)%L, then for lo ≤ i < j ≤ mid, (i+k)%L < (j+k)%L

PROVIDED SOLUTION
We need to show (i+k)%L < (j+k)%L given that (lo+k)%L ≤ (mid+k)%L and lo ≤ i < j ≤ mid.

Key idea: Consider two cases:
Case 1: (lo+k) % L ≤ (mid+k) % L means there's no wrap in going from lo+k to mid+k modulo L. Since lo ≤ i < j ≤ mid, we have lo+k ≤ i+k < j+k ≤ mid+k. If (lo+k)%L ≤ (mid+k)%L, then either:
  (a) lo+k < L, so no values in [lo+k, mid+k] wrap around, and %L is the identity on this range. Then (i+k)%L = i+k < j+k = (j+k)%L.
  (b) All values in [lo+k, mid+k] are ≥ L, so after subtracting L they're in [lo+k-L, mid+k-L] which is < L (since mid < L and k can be at most L-1 by periodicity). Then (i+k)%L = i+k-L < j+k-L = (j+k)%L.
  (c) Some values are < L and some ≥ L (wrap point in range). But then (lo+k)%L = lo+k while (mid+k)%L = mid+k-L, and lo+k > mid+k-L since mid+k-L < lo+k ≤ mid+k. Wait, we'd need lo+k < L ≤ mid+k. Then (lo+k)%L = lo+k and (mid+k)%L = mid+k - L. For the non-wrapping condition, we need lo+k ≤ mid+k - L, i.e., L ≤ mid - lo. But mid < L so mid - lo < L, contradiction. So case (c) leads to (lo+k)%L > (mid+k)%L, contradicting the hypothesis.

So we're in case (a) or (b), and in both cases the %L function is monotone on [lo+k, mid+k], giving the result.

Actually simpler: We can use the fact that for a, b with a ≤ b and (a%L) ≤ (b%L), and any c with a ≤ c ≤ b, we have a%L ≤ c%L ≤ b%L. This is because (a%L) ≤ (b%L) means there's no wrap in [a, b], so the floor(·/L) is the same for all values in [a, b], making %L monotone.

Use omega or Nat.mod properties to formalize this.
-/
lemma mod_mono_in_range (L k lo mid i j : ℕ) (hL : L > 0)
    (hlo_le_mid : lo ≤ mid) (hmid_lt : mid < L)
    (h_no_wrap : (lo + k) % L ≤ (mid + k) % L)
    (hlo_le_i : lo ≤ i) (hi_lt_j : i < j) (hj_le_mid : j ≤ mid) :
    (i + k) % L < (j + k) % L := by
  by_cases h_case : (i + k) / L = (j + k) / L;
  · nlinarith [ Nat.mod_add_div ( i + k ) L, Nat.mod_add_div ( j + k ) L ];
  · have h_floor_eq : (lo + k) / L = (mid + k) / L := by
      by_contra h_contra;
      exact h_contra <| by nlinarith [ Nat.mod_add_div ( lo + k ) L, Nat.mod_add_div ( mid + k ) L, Nat.mod_lt ( lo + k ) hL, Nat.mod_lt ( mid + k ) hL, show ( lo + k ) / L < ( mid + k ) / L from lt_of_le_of_ne ( Nat.div_le_div_right <| by linarith ) h_contra ] ;
    have h_floor_eq : (lo + k) / L ≤ (i + k) / L ∧ (i + k) / L ≤ (j + k) / L ∧ (j + k) / L ≤ (mid + k) / L := by
      exact ⟨ Nat.div_le_div_right ( by linarith ), Nat.div_le_div_right ( by linarith ), Nat.div_le_div_right ( by linarith ) ⟩;
    grind

lemma rotated_sorted_segment_strict_mono (nums : List ℤ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (lo mid : ℕ) (hlo_le_mid : lo ≤ mid) (hmid_lt : mid < nums.length) (h_sorted_seg : nums[lo]'(by omega) ≤ nums[mid]'hmid_lt) (i j : ℕ) (hlo_le_i : lo ≤ i) (hi_lt_j : i < j) (hj_le_mid : j ≤ mid) : nums[i]'(by omega) < nums[j]'(by omega) := by
  obtain ⟨base, hbase_sorted, hbase_nodup, hbase_rot⟩ := h_rot
  obtain ⟨k, hk⟩ := hbase_rot
  have hlen : nums.length = base.length := by rw [← hk, List.length_rotate]
  have hL : base.length > 0 := by omega
  have h_no_wrap := rotation_no_wrap_of_le base k hbase_sorted hbase_nodup nums hk lo mid (by omega) hmid_lt hlo_le_mid h_sorted_seg
  have h_idx := mod_mono_in_range base.length k lo mid i j hL hlo_le_mid (by omega) h_no_wrap hlo_le_i hi_lt_j hj_le_mid
  exact rotation_preserves_order base k hbase_sorted nums hk i j (by omega) (by omega) hi_lt_j h_idx

lemma rotated_sorted_no_descent_segment (nums : List ℤ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (i j : ℕ) (hi_lt : i < nums.length) (hj_lt : j < nums.length) (hij : i < j) (h_le : nums[i]'hi_lt ≤ nums[j]'hj_lt) (p : ℕ) (hip : i ≤ p) (hpj : p < j) : nums[p]'(by omega) < nums[p+1]'(by omega) := by
  have := rotated_sorted_segment_strict_mono
  contrapose! this
  use nums, h_nodup, h_rot, i, j, by linarith, by linarith, by linarith, p, p + 1, by linarith, by linarith, by linarith, by linarith

/-
PROVIDED SOLUTION
By contradiction: assume n ≥ mid. Since mid ≠ n, we have n > mid. So lo ≤ mid < n and both are < nums.length.

Since nums[lo] ≤ nums[n] (from h_target_in_left.1), and lo ≤ n, by rotated_sorted_segment_strict_mono (with lo := lo, mid := n, i := mid, j := n), we'd need nums[lo] ≤ nums[n], which we have. Then rotated_sorted_segment_strict_mono gives nums[mid] < nums[n].

But h_target_in_left.2 says nums[n] < nums[mid], contradiction.

Wait, let me be more careful. We need rotated_sorted_segment_strict_mono applied with:
- lo_param = lo, mid_param = n (the "sorted segment" endpoints)
- h_sorted_seg: nums[lo] ≤ nums[n] (from h_target_in_left.1)
- i_param = mid, j_param = n
- This gives nums[mid] < nums[n]
But h_target_in_left.2 gives nums[n] < nums[mid], contradiction.
-/
lemma rotated_sorted_left_sorted_range (nums : List ℤ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (lo mid hi n : ℕ) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hhi_le : hi ≤ nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hmid_ne_n : mid ≠ n) (hlo_lt_len : lo < nums.length) (hmid_lt_len : mid < nums.length) (h_left_sorted : nums[lo]'hlo_lt_len ≤ nums[mid]'hmid_lt_len) (h_target_in_left : nums[lo]'hlo_lt_len ≤ nums[n]'(by omega) ∧ nums[n]'(by omega) < nums[mid]'hmid_lt_len) : n < mid := by
  -- By contradiction, assume $mid \leq n$.
  by_contra h_not_lt;
  -- By the rotated_sorted_segment_strict_mono lemma, since nums[lo] ≤ nums[n] and lo ≤ n, we have nums[mid] < nums[n].
  have h_mid_lt_n : nums[mid] < nums[n] := by
    apply rotated_sorted_segment_strict_mono nums h_nodup h_rot lo n hlo_le_n (by omega) (by omega) mid n (by omega) (by omega) (by omega);
  linarith

/-
PROVIDED SOLUTION
The first part (lo ≤ n) is given directly by hlo_le_n. For the second part (n < mid), substitute target = nums[n] (from hn_getElem) into h_in_left to get nums[lo] ≤ nums[n] and nums[n] < nums[mid]. Then apply rotated_sorted_left_sorted_range with the appropriate arguments.
-/
lemma searchHelper_invariant_left_sorted (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hn_lt : n < nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hmid_ne_n : mid ≠ n) (hn_getElem : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target) (hlo_lt : lo < nums.length) (h_left_sorted : nums[lo]'hlo_lt ≤ nums[mid]'(by omega)) (h_in_left : nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega)) : lo ≤ n ∧ n < mid := by
  apply And.intro hlo_le_n;
  apply rotated_sorted_left_sorted_range nums h_nodup h_rot lo mid hi n hlo_le_mid hmid_lt_hi hhi_le hlo_le_n hn_lt_hi hmid_ne_n hlo_lt (by
  grind) h_left_sorted (by
  aesop)

/-
PROBLEM
Part 1: left half sorted and target in left range → n < mid

PROVIDED SOLUTION
This is the same as rotated_sorted_left_sorted_range / searchHelper_invariant_left_sorted. Since nums[lo] ≤ nums[mid] (left half sorted), and target = nums[n] with nums[lo] ≤ target < nums[mid], we need n < mid. Apply rotated_sorted_left_sorted_range with appropriate arguments.

Alternatively, by contradiction: if n ≥ mid, then since n ≠ mid we have n > mid. Since nums[lo] ≤ nums[n] (= target), by rotated_sorted_segment_strict_mono with sorted segment [lo, n], we get nums[mid] < nums[n]. But nums[n] = target < nums[mid], contradiction.
-/
lemma branch_part1 (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hn_lt : n < nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hmid_ne_n : mid ≠ n) (hn_val : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target) (hlo_lt : lo < nums.length)
    (h_left_sorted : nums[lo]'hlo_lt ≤ nums[mid]'(by omega))
    (h_in_left : nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega)) :
    n < mid := by
  apply rotated_sorted_left_sorted_range;
  all_goals try assumption;
  aesop

/-
PROBLEM
Part 2: left half sorted and target NOT in left range → mid < n

PROVIDED SOLUTION
By contradiction: if n ≤ mid, then since n ≠ mid we have n < mid. Since the left half [lo..mid] is sorted (nums[lo] ≤ nums[mid]), by rotated_sorted_segment_strict_mono:
- lo ≤ n < mid implies nums[lo] ≤ nums[n] (since lo ≤ n ≤ mid and the segment is monotone; specifically for lo < n use strict_mono, for lo = n it's trivial)
- Also nums[n] < nums[mid] (by strict_mono since n < mid)

Wait, more carefully: if lo = n then nums[lo] = nums[n] = target ≤ target, so nums[lo] ≤ target. If lo < n ≤ mid, then rotated_sorted_segment_strict_mono gives nums[lo] < nums[n], so nums[lo] ≤ target = nums[n].

Also, if n < mid, rotated_sorted_segment_strict_mono gives nums[n] < nums[mid], so target < nums[mid].

So nums[lo] ≤ target and target < nums[mid], meaning target ∈ [nums[lo], nums[mid]), contradicting h_not_in_left.

If n = mid, then nums[n] = nums[mid] but hn_val says nums[n] = target and hmid_neq_target says nums[mid] ≠ target, contradiction. So n > mid.
-/
lemma branch_part2 (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hn_lt : n < nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hmid_ne_n : mid ≠ n) (hn_val : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target) (hlo_lt : lo < nums.length)
    (h_left_sorted : nums[lo]'hlo_lt ≤ nums[mid]'(by omega))
    (h_not_in_left : ¬(nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega))) :
    mid < n := by
  contrapose! h_not_in_left;
  have := @rotated_sorted_segment_strict_mono nums h_nodup h_rot lo mid hlo_le_mid ( by linarith ) ( by aesop );
  by_cases h_cases : lo < n;
  · exact ⟨ hn_val ▸ le_of_lt ( this _ _ le_rfl h_cases ( by linarith ) ), hn_val ▸ this _ _ ( by linarith ) ( lt_of_le_of_ne ( by linarith ) ( by aesop ) ) ( by linarith ) ⟩;
  · grind

/-
PROBLEM
Helper: when nums[lo] > nums[mid], the segment [mid, hi-1] is strictly sorted
(the pivot is in the left half, so the right half has no wrap)

PROVIDED SOLUTION
We have nums = base.rotate k for some strictly sorted base. nums[lo] > nums[mid] means (lo+k)%L > (mid+k)%L (using contrapositive of rotation_no_wrap_of_le, since if (lo+k)%L ≤ (mid+k)%L then by rotation_preserves_order we'd get nums[lo] ≤ nums[mid] when lo < mid, or equality when lo = mid; either way contradicting h_unsorted).

Now for mid ≤ i < j < L: we need (i+k)%L < (j+k)%L. Since (lo+k)%L > (mid+k)%L, the wrap point (where (p+k) crosses L) is in [lo, mid-1]. For indices p ≥ mid, (p+k) is past the wrap, so (p+k)%L = (p+k) - L (or (p+k)%L = (p+k) if p+k < L). Since there's no wrap in [mid, L-1], the function p ↦ (p+k)%L is strictly increasing on [mid, L-1].

More concretely: (lo+k)%L > (mid+k)%L implies that (lo+k) and (mid+k) are in different "cycles" modulo L, meaning (lo+k)/L < (mid+k)/L (otherwise same quotient gives lo+k < mid+k implies (lo+k)%L < (mid+k)%L). So (mid+k)/L ≥ (lo+k)/L + 1. Since lo ≤ mid, (mid+k) - (lo+k) = mid - lo ≤ L-1, so (mid+k)/L = (lo+k)/L + 1 (can't differ by more than 1). For j ≥ i ≥ mid, (j+k) ≥ (i+k) ≥ (mid+k), and (j+k) ≤ (L-1+k). Since (mid+k)/L = (lo+k)/L + 1 and mid ≤ i < j < L, we need to show (i+k)/L = (j+k)/L (same quotient), which gives (i+k)%L < (j+k)%L.

(i+k)/L ≥ (mid+k)/L = (lo+k)/L + 1. Also (j+k) ≤ (L-1)+k, and ((L-1)+k)/L ≤ ((lo+k)/L + 1) since (L-1+k) - L*(lo+k)/L ≤ L-1+k - (lo+k - (L-1)) = 2L - 2 - lo. Hmm this is getting complicated.

Simpler: Use mod_mono_in_range or a similar argument. The key is that (lo+k)%L > (mid+k)%L means the wrap is in [lo+k, mid+k], so for p+k ≥ mid+k, we're past the wrap, and (p+k)/L is constant (same quotient) for all p in [mid, L-1]. Therefore %L is strictly monotone on [mid, L-1].

Actually, even simpler: just use rotation_preserves_order + rotation_no_wrap_of_le's contrapositive directly. We know (lo+k)%L > (mid+k)%L. For mid ≤ i < j < L, suppose for contradiction (i+k)%L ≥ (j+k)%L. Since i < j, (i+k) < (j+k). For (i+k)%L ≥ (j+k)%L with i+k < j+k, the wrap must be in [i+k, j+k-1], meaning mid ≤ i < j ≤ L-1 and there's a wrap at some point. But if there's already a wrap in [lo+k, mid+k-1] and another in [i+k, j+k-1], that would require two wraps, which is impossible if j-1 < L (since j < L, j+k < 2L, so at most one wrap). Actually with lo ≤ mid ≤ i, and both wrapping, the two wrap points would be the same since there can only be one modular wrap in [lo+k, j+k-1]. But the wrap in [lo+k, mid+k-1] means (lo+k) < L ≤ (mid+k) (approximately), and the wrap in [i+k, j+k-1] means some (p+k) < L ≤ (p+1+k). But if mid+k ≥ L (from the first wrap) and i ≥ mid, then i+k ≥ L, so (i+k)%L = i+k-L and (j+k)%L = j+k-L (both past the wrap), giving (i+k)%L < (j+k)%L. Contradiction with our assumption.

So for mid ≤ i < j < L with (lo+k)%L > (mid+k)%L, we get (i+k)%L < (j+k)%L. Then by sorted_base_strict_lt, base[(i+k)%L] < base[(j+k)%L], i.e., nums[i] < nums[j].
-/
lemma right_half_sorted_of_left_unsorted (nums : List ℤ) (h_nodup : nums.Nodup)
    (h_rot : isRotationOfStrictSorted nums)
    (lo mid : ℕ) (hlo_le_mid : lo ≤ mid) (hmid_lt : mid < nums.length)
    (h_unsorted : nums[lo]'(by omega) > nums[mid]'hmid_lt)
    (i j : ℕ) (hmid_le_i : mid ≤ i) (hi_lt_j : i < j) (hj_lt : j < nums.length) :
    nums[i]'(by omega) < nums[j]'(by omega) := by
  -- Since nums is a rotation of a strictly sorted base list, there exists a base list base and an index k such that nums = base.rotate k.
  obtain ⟨base, k, hbase⟩ : ∃ base : List ℤ, ∃ k : ℕ, base.Nodup ∧ isStrictSorted base ∧ nums = base.rotate k := by
    obtain ⟨ base, hbase₁, hbase₂, hbase₃ ⟩ := h_rot;
    rcases hbase₃ with ⟨ k, hk ⟩ ; use base, k ; aesop;
  -- Since (lo + k) % base.length < (mid + k) % base.length, we have (i + k) % base.length < (j + k) % base.length for any mid ≤ i < j < base.length.
  have h_mod_lt : (i + k) % base.length < (j + k) % base.length := by
    have h_mod_lt : (lo + k) % base.length > (mid + k) % base.length := by
      have h_left_wrap : (lo + k) % base.length ≠ (mid + k) % base.length := by
        intro h; simp_all +decide [ List.getElem_rotate ] ;
      cases lt_or_gt_of_ne h_left_wrap <;> simp_all +decide [ List.getElem_rotate ];
      exact absurd h_unsorted ( not_lt_of_ge ( sorted_base_strict_lt _ hbase.2.1 _ _ ( Nat.mod_lt _ ( by linarith ) ) ( Nat.mod_lt _ ( by linarith ) ) ( by assumption ) |> le_of_lt ) );
    -- Since there's a wrap in [lo + k, mid + k], for any i ≥ mid, (i + k) is past the wrap, so (i + k) % base.length = (i + k) - base.length.
    have h_mod_eq : ∀ i, mid ≤ i → i < base.length → (i + k) % base.length = (i + k) - base.length * ((mid + k) / base.length) := by
      intros i hi mid_lt_base
      have h_mod_eq : (i + k) / base.length = (mid + k) / base.length := by
        have h_mod_eq : (lo + k) / base.length < (mid + k) / base.length := by
          contrapose! h_mod_lt;
          rw [ Nat.mod_eq_sub_mul_div, Nat.mod_eq_sub_mul_div ];
          exact Nat.sub_le_sub_right ( by nlinarith [ Nat.div_mul_le_self ( lo + k ) base.length, Nat.div_mul_le_self ( mid + k ) base.length ] ) _ |> le_trans <| Nat.sub_le_sub_left ( Nat.mul_le_mul_left _ h_mod_lt ) _;
        have h_mod_eq : (mid + k) / base.length = (lo + k) / base.length + 1 := by
          have h_mod_eq : (mid + k) / base.length ≤ (lo + k) / base.length + 1 := by
            exact Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_add_mod ( lo + k ) base.length, Nat.mod_lt ( lo + k ) ( show base.length > 0 from Nat.pos_of_ne_zero <| by aesop_cat ) ] ;
          linarith;
        have h_mod_eq : (i + k) / base.length ≤ (mid + k) / base.length := by
          rw [ h_mod_eq ];
          rw [ Nat.div_le_iff_le_mul_add_pred ];
          · linarith [ Nat.div_add_mod ( lo + k ) base.length, Nat.mod_lt ( lo + k ) ( by linarith : 0 < base.length ), Nat.sub_add_cancel ( by linarith : 1 ≤ base.length ) ];
          · linarith;
        exact le_antisymm h_mod_eq ( by exact Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero ( by aesop_cat ) ) |>.2 ( by linarith [ Nat.div_mul_le_self ( lo + k ) base.length, Nat.div_mul_le_self ( mid + k ) base.length, Nat.mod_add_div ( lo + k ) base.length, Nat.mod_add_div ( mid + k ) base.length ] ) );
      rw [ ← h_mod_eq, Nat.mod_eq_sub_mul_div ];
    rw [ h_mod_eq i hmid_le_i, h_mod_eq j ( by linarith ) ( by simpa [ hbase ] using hj_lt ) ];
    · rw [ tsub_lt_tsub_iff_right ] <;> try linarith;
      nlinarith [ Nat.div_mul_le_self ( mid + k ) base.length ];
    · rw [ hbase.2.2, List.length_rotate ] at hj_lt ; linarith;
  convert sorted_base_strict_lt base hbase.2.1 _ _ _ _ _ using 1;
  all_goals norm_num [ List.getElem_rotate, hbase.2.2 ] at *;
  all_goals norm_cast

/-
PROBLEM
Part 3: right half sorted and target in right range → mid < n

PROVIDED SOLUTION
By contradiction, assume n ≤ mid, so n < mid (since n ≠ mid). lo ≤ n < mid.

Since nums[lo] > nums[mid] (from push_neg of h_right_sorted), the right segment [mid, hi-1] is strictly sorted by right_half_sorted_of_left_unsorted.

Now, n < mid. We need to show this is impossible given that target = nums[n], target > nums[mid], and target ≤ nums[hi-1].

Case 1: nums[n] ≤ nums[mid]. Then target = nums[n] ≤ nums[mid], contradicting target > nums[mid] (from h_in_right.1).

Case 2: nums[n] > nums[mid]. Since n < mid, and both are in [lo, mid], with nums[lo] > nums[mid]... Actually, we need to be more careful. In a rotated sorted array with nums[lo] > nums[mid], the segment [lo, mid] wraps. So nums[n] could be either > nums[mid] (before pivot) or ≤ nums[mid] (after pivot).

If nums[n] > nums[mid] (before pivot): Since n is before the pivot, all values before the pivot are ≥ the minimum of the "high" part. The key fact: in a rotation by k of base[0..L-1], the "high" segment goes from index (L-k)%L to L-1 in base, and corresponds to indices 0 to k-1 in nums. The "low" segment goes from 0 to L-k-1 in base, corresponding to indices k to L-1 in nums.

Actually, the simplest argument is: use right_half_sorted_of_left_unsorted to show the entire segment from mid to L-1 is sorted. Then use the rotation structure to show that ALL values in [mid, L-1] are strictly less than ALL values in [0, lo] (or more precisely, lo is in the "high" part).

Hmm, this is getting complicated. Let me use a more direct approach.

Key insight: From right_half_sorted_of_left_unsorted, for mid ≤ p < q < nums.length, nums[p] < nums[q]. In particular, nums[mid] < nums[hi-1] (when mid < hi-1).

Also, from the rotation structure, for 0 ≤ p < q ≤ lo with nums[lo] > nums[mid], we have... hmm.

Actually, let me use the following approach:
1. The entire array has exactly one descent (where nums[p] > nums[p+1]).
2. This descent is in [lo, mid-1] (since nums[lo] > nums[mid] forces a descent in this range).
3. Therefore, there's no descent in [0, lo-1] ∪ [mid, L-1] → these segments are increasing.
4. For n in [lo, mid-1]: if n is before the descent point, nums[n] ≥ nums[lo]. If n is after the descent point, nums[n] ≤ nums[mid].

If n is after the descent: nums[n] ≤ nums[mid], so target ≤ nums[mid], contradicting target > nums[mid].
If n is before the descent: nums[n] ≥ nums[lo] > nums[mid]. Also nums[n] ≥ nums[lo]. But what about target ≤ nums[hi-1]? Since nums[hi-1] < nums[lo] (because all post-descent values < all pre-descent values in a rotated sorted array), nums[n] ≥ nums[lo] > nums[hi-1] ≥ target, contradicting target = nums[n].

Wait, is nums[hi-1] < nums[lo] necessarily? In a rotated sorted array, the values after the descent point are all < the values before it (they come from the beginning of the sorted base array, while the values before come from the end). So yes, nums[hi-1] (after descent) < nums[lo] (before descent).

But I need to establish this formally. Let me use the fact that the segment from mid to hi-1 is sorted, and all of these values come from the "low" part of base. Meanwhile, nums[lo] comes from the "high" part of base. Since base is sorted, all high-part values > all low-part values.

More concretely: using right_half_sorted_of_left_unsorted, we can show the segment [mid, nums.length-1] is sorted (if mid ≤ lo ≤ nums.length-1... no, we need mid ≤ i < j < nums.length).

Actually, right_half_sorted_of_left_unsorted gives us: for mid ≤ i < j < nums.length, nums[i] < nums[j]. In particular, nums[mid] < nums[nums.length-1].

Now, what about the segment [0, lo]? We need: for 0 ≤ i < j ≤ lo, nums[i] < nums[j]. Hmm, we don't have a direct lemma for this.

But we do have: in the rotation, there's exactly one wrap in base indices. The wrap is in [lo, mid-1]. So:
- For indices in [0, lo-1] and [mid, L-1]: no wrap, base indices are monotonically increasing.
- The maximum base index before the wrap is at lo (or wherever the wrap starts), and the minimum after is at mid.

This is getting complex. Let me just provide the key lemma references and a short hint, and give the subagent more budget by breaking this into even smaller pieces.

Actually, let me try a cleaner approach. I'll add a helper lemma that directly captures: in a rotated sorted array, if nums[lo] > nums[mid], then for lo ≤ n < mid, nums[n] is NOT in (nums[mid], nums[hi-1]].

This would directly give branch_part3 (by contradiction).
-/
lemma branch_part3 (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hn_lt : n < nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hmid_ne_n : mid ≠ n) (hn_val : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target) (hlo_lt : lo < nums.length)
    (h_right_sorted : ¬(nums[lo]'hlo_lt ≤ nums[mid]'(by omega)))
    (h_in_right : nums[mid]'(by omega) < target ∧ target ≤ nums[hi - 1]'(by omega)) :
    mid < n := by
  contrapose! h_right_sorted;
  cases lt_or_eq_of_le h_right_sorted <;> simp_all +decide [ List.getElem?_eq_getElem ];
  -- Since $n < mid$, we have $nums[n] < nums[mid]$ by the properties of the sorted array.
  have h_lt_mid : nums[n]'hn_lt < nums[mid]'(by omega) := by
    apply rotated_sorted_segment_strict_mono;
    grind;
    exact h_rot;
    convert h_in_right.2;
    · linarith;
    · linarith;
    · exact Nat.le_pred_of_lt hmid_lt_hi;
    · omega;
  grind

/-
PROBLEM
Part 4: right half sorted and target NOT in right range → n < mid

PROVIDED SOLUTION
By contradiction, assume n ≥ mid, so n > mid (since n ≠ mid). Then mid < n < hi ≤ nums.length.

Since nums[lo] > nums[mid] (from push_neg of h_right_sorted), by right_half_sorted_of_left_unsorted, the segment [mid, L-1] is strictly sorted. In particular, for mid < n < hi:
- nums[mid] < nums[n] (since mid < n and both are in the sorted right segment)
- If n < hi-1: nums[n] < nums[hi-1], so nums[n] ≤ nums[hi-1]
- If n = hi-1: nums[n] = nums[hi-1] ≤ nums[hi-1]

So target = nums[n] satisfies: nums[mid] < target (from above) and target ≤ nums[hi-1].
This means nums[mid] < target ∧ target ≤ nums[hi-1] is true, contradicting h_not_in_right.
-/
lemma branch_part4 (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hn_lt : n < nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hmid_ne_n : mid ≠ n) (hn_val : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target) (hlo_lt : lo < nums.length)
    (h_right_sorted : ¬(nums[lo]'hlo_lt ≤ nums[mid]'(by omega)))
    (h_not_in_right : ¬(nums[mid]'(by omega) < target ∧ target ≤ nums[hi - 1]'(by omega))) :
    n < mid := by
  -- If $n \geq mid$, then $nums[mid] < nums[n]$ because $nums[mid] \neq target$ and $nums[n] = target$.
  by_cases hnm : n ≥ mid
  have hmn : nums[mid] < nums[n] := by
    apply right_half_sorted_of_left_unsorted nums h_nodup h_rot lo mid hlo_le_mid (by omega) (by
    grind +ring) mid n (by
    exact le_rfl) (by
    exact lt_of_le_of_ne hnm hmid_ne_n) (by
    linarith)
  generalize_proofs at *; (
  -- Since $n \geq mid$, we have $nums[mid] < nums[n]$ because $nums[mid] \neq target$ and $nums[n] = target$.
  by_cases hnm' : n < hi - 1
  generalize_proofs at *; (
  have hmn' : nums[n] < nums[hi - 1] := by
    apply right_half_sorted_of_left_unsorted nums h_nodup h_rot lo mid hlo_le_mid (by omega) (by
    exact lt_of_not_ge h_right_sorted) n (hi - 1) (by omega) (by omega) (by omega)
  generalize_proofs at *; (
  exact False.elim <| h_not_in_right ⟨ by linarith, by linarith ⟩ ;));
  grind); (
  exact lt_of_not_ge hnm)

lemma rotated_binary_search_branch_invariant (nums : List ℤ) (target : ℤ) (n lo mid hi : ℕ) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hn_lt : n < nums.length) (hlo_le_n : lo ≤ n) (hn_lt_hi : n < hi) (hhi_le : hi ≤ nums.length) (hlo_le_mid : lo ≤ mid) (hmid_lt_hi : mid < hi) (hmid_ne_n : mid ≠ n) (hn_val : nums[n]'hn_lt = target)
    (hmid_neq_target : nums[mid]'(by omega) ≠ target) (hlo_lt : lo < nums.length) : (nums[lo]'hlo_lt ≤ nums[mid]'(by omega) →
     (nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega)) →
     n < mid) ∧
    (nums[lo]'hlo_lt ≤ nums[mid]'(by omega) →
     ¬(nums[lo]'hlo_lt ≤ target ∧ target < nums[mid]'(by omega)) →
     mid < n) ∧
    (¬(nums[lo]'hlo_lt ≤ nums[mid]'(by omega)) →
     (nums[mid]'(by omega) < target ∧ target ≤ nums[hi - 1]'(by omega)) →
     mid < n) ∧
    (¬(nums[lo]'hlo_lt ≤ nums[mid]'(by omega)) →
     ¬(nums[mid]'(by omega) < target ∧ target ≤ nums[hi - 1]'(by omega)) →
     n < mid) := by
  exact ⟨branch_part1 nums target n lo mid hi h_nodup h_rot hn_lt hlo_le_n hn_lt_hi hhi_le hlo_le_mid hmid_lt_hi hmid_ne_n hn_val hmid_neq_target hlo_lt,
         branch_part2 nums target n lo mid hi h_nodup h_rot hn_lt hlo_le_n hn_lt_hi hhi_le hlo_le_mid hmid_lt_hi hmid_ne_n hn_val hmid_neq_target hlo_lt,
         branch_part3 nums target n lo mid hi h_nodup h_rot hn_lt hlo_le_n hn_lt_hi hhi_le hlo_le_mid hmid_lt_hi hmid_ne_n hn_val hmid_neq_target hlo_lt,
         branch_part4 nums target n lo mid hi h_nodup h_rot hn_lt hlo_le_n hn_lt_hi hhi_le hlo_le_mid hmid_lt_hi hmid_ne_n hn_val hmid_neq_target hlo_lt⟩

/-
PROVIDED SOLUTION
Prove by strong induction on (hi - lo). The base case hi ≤ lo gives n < hi ≤ lo ≤ n, contradiction (so vacuously true, or use omega).

For the inductive step (lo < hi):
1. Unfold searchHelper: by the definition, since lo < hi, compute mid = lo + (hi - lo) / 2.
2. Show mid < arr.size (since mid < hi ≤ arr.size).
3. Check if arr[mid] == target:
   - If arr[mid] = target (BEq): then mid = n (by h_unique, since both arr[mid] and arr[n] equal target, where arr = nums.toArray). Result is Int.ofNat mid = Int.ofNat n.
   - If arr[mid] ≠ target: then mid ≠ n. Check if lo < arr.size (yes, since lo < hi ≤ arr.size).
     Now branch on the 4 cases using rotated_binary_search_branch_invariant:
     a. arr[lo] ≤ arr[mid] and arr[lo] ≤ target < arr[mid]: recurse on (lo, mid). By branch invariant part 1, n < mid. By IH (hi decreased to mid), searchHelper returns n.
     b. arr[lo] ≤ arr[mid] and ¬(arr[lo] ≤ target < arr[mid]): recurse on (mid+1, hi). By branch invariant part 2, mid < n, i.e., n ≥ mid+1. By IH, searchHelper returns n.
     c. ¬(arr[lo] ≤ arr[mid]) and arr[mid] < target ≤ arr[hi-1]: recurse on (mid+1, hi). By branch invariant part 3, mid < n. By IH, searchHelper returns n.
     d. ¬(arr[lo] ≤ arr[mid]) and ¬(arr[mid] < target ≤ arr[hi-1]): recurse on (lo, mid). By branch invariant part 4, n < mid. By IH, searchHelper returns n.

Key: Use simp to unfold searchHelper, handle the BEq check (arr[mid] == target uses BEq for Int which is decidable), and carefully apply the inductive hypothesis.

Note: arr = nums.toArray, so arr.size = nums.length, and arr[i] = nums[i] for valid i. Use Array.getElem_toArray or List.getElem_toArray to convert.

The induction is on (hi - lo) since each recursive call strictly decreases this quantity.
-/
theorem correctness_goal_1_0 (nums : List ℤ) (target : ℤ) (h_len : nums.length > 0) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hmem : target ∈ nums) (n : ℕ) (hn_eq : nums[n]? = some target) (hn_lt : n < nums.length) (hn_val : nums[n]? = some target) (h_unique : ∀ j < nums.length, nums[j]? = some target → j = n) : ∀ (lo hi : ℕ), lo ≤ n → n < hi → hi ≤ nums.toArray.size → searchHelper nums.toArray target lo hi = Int.ofNat n := by
    intros lo hi hlo hn_lt hhi_le
    induction' k : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi;
    unfold searchHelper;
    have := rotated_binary_search_branch_invariant nums target n lo ( lo + ( hi - lo ) / 2 ) hi h_nodup h_rot ‹_› ‹_› ‹_› ?_ ?_ ?_ <;> norm_num at *;
    any_goals omega;
    grind

end Proof