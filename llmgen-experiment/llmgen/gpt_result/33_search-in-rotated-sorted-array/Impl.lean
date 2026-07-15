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
  -- Convert once to Array for O(1) indexing; overall O(log n) time, O(1) extra space besides this conversion.
  let arr : Array Int := nums.toArray
  let n : Nat := arr.size

  -- Standard binary search on rotated strictly-increasing array with distinct elements.
  let mut lo : Nat := 0
  let mut hi : Nat := n
  let mut ans : Int := (-1)

  while lo < hi
    -- Bounds: keep the current search interval within [0,n].
    -- Init: lo=0, hi=n. Preserved: each branch shrinks [lo,hi) without leaving bounds.
    invariant "inv_bounds" lo ≤ hi ∧ hi ≤ n
    -- n is a fixed alias for arr.size.
    invariant "inv_n_size" n = arr.size
    -- Bridge array bounds back to the list-based postcondition.
    invariant "inv_len" n = nums.length
    -- Answer soundness: if ans is not -1, it points to an index where target occurs in nums.
    -- Init: ans=-1. Preserved: only set when midVal=target, and then ans=Int.ofNat mid.
    invariant "inv_ans_sound" (ans = (-1)) ∨ (∃ i : Nat, i < nums.length ∧ nums.get? i = some target ∧ ans = Int.ofNat i)
    -- Completeness wrt the remaining search interval: if target is in nums and we haven't found it yet,
    -- then it must occur somewhere in the current interval [lo, hi) in arr.
    -- At loop exit with lo=hi, this implies: ans=-1 → target ∉ nums, which discharges the -1 case.
    invariant "inv_search_space" (ans = (-1) ∧ inList nums target) → (∃ k : Nat, lo ≤ k ∧ k < hi ∧ arr[k]! = target)
    -- Control-flow fact: once we record an answer we immediately force lo=hi, so the loop stops.
    invariant "inv_found_forces_exit" (ans ≠ (-1)) → lo = hi
    decreasing hi - lo
  do
    let mid : Nat := lo + (hi - lo) / 2
    let midVal : Int := arr[mid]!

    if midVal = target then
      ans := Int.ofNat mid
      -- Found; force termination without early return.
      lo := hi
    else
      let loVal : Int := arr[lo]!
      -- Determine which half is sorted and narrow search accordingly.
      if loVal <= midVal then
        -- Left half [lo, mid] is sorted.
        if loVal <= target ∧ target < midVal then
          hi := mid
        else
          lo := mid + 1
      else
        -- Right half [mid, hi) is sorted.
        let hi1 : Nat := hi - 1
        let hiVal : Int := arr[hi1]!
        if midVal < target ∧ target <= hiVal then
          lo := mid + 1
        else
          hi := mid

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
    (if_pos : lo < hi)
    (a_1 : hi ≤ nums.length)
    : lo.cast + (hi - lo).cast / (2 : ℤ) = -(1 : ℤ) ∨ ∃ i < nums.length, nums[i]? = some (nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) ∧ lo.cast + (hi - lo).cast / (2 : ℤ) = i.cast := by
    apply Or.inr
    have hlo_le : lo ≤ hi := Nat.le_of_lt if_pos
    have hmid_lt : lo + (hi - lo) / 2 < nums.length := by omega
    refine ⟨lo + (hi - lo) / 2, hmid_lt, ?_, ?_⟩
    · simp [List.getElem?_eq_getElem hmid_lt]
    · push_cast [Nat.cast_sub hlo_le]
      rfl

theorem goal_1_0
    (nums : List ℤ)
    (target : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (a_1 : hi ≤ nums.length)
    (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target)
    (a_3 : target < nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (k : ℕ)
    (hkhi : k < hi)
    (hkval : nums[k]?.getD (OfNat.ofNat 0) = target)
    : k < lo + (hi - lo) / 2 := by
  classical
  let mid : Nat := lo + (hi - lo) / 2

  have hlo_len : lo < nums.length := lt_of_lt_of_le if_pos a_1
  have hk_len : k < nums.length := lt_of_lt_of_le hkhi a_1

  have hhalf_lt : (hi - lo) / 2 < (hi - lo) := by
    have hpos : 0 < hi - lo := Nat.sub_pos_of_lt if_pos
    simpa using (Nat.div_lt_self hpos (by decide : 1 < (2:Nat)))

  have hmid_lt_hi : mid < hi := by
    have : lo + (hi - lo) / 2 < lo + (hi - lo) := Nat.add_lt_add_left hhalf_lt lo
    simpa [mid, Nat.add_sub_of_le a] using this
  have hmid_len : mid < nums.length := lt_of_lt_of_le hmid_lt_hi a_1

  have hmid_ge_lo : lo ≤ mid := by
    simp [mid]

  -- simplify the getD expressions
  have h_lo_getD : nums[lo]?.getD (0:ℤ) = nums[lo]'hlo_len := by
    simp [List.getElem?_eq_getElem hlo_len]
  have h_mid_getD : nums[mid]?.getD (0:ℤ) = nums[mid]'hmid_len := by
    simp [List.getElem?_eq_getElem hmid_len]
  have h_k_getD : nums[k]?.getD (0:ℤ) = nums[k]'hk_len := by
    simp [List.getElem?_eq_getElem hk_len]

  have hlo_mid_le : nums[lo]'hlo_len ≤ nums[mid]'hmid_len := by
    simpa [mid, h_lo_getD, h_mid_getD] using if_pos_1
  have hlo_le_target : nums[lo]'hlo_len ≤ target := by
    simpa [h_lo_getD] using a_2
  have htarget_lt_mid : target < nums[mid]'hmid_len := by
    simpa [mid, h_mid_getD] using a_3
  have hmid_ne_target : nums[mid]'hmid_len ≠ target := by
    simpa [mid, h_mid_getD] using if_neg
  have hk_val : nums[k]'hk_len = target := by
    simpa [h_k_getD] using hkval

  -- rotation structure
  rcases require_1 with ⟨hlen_pos, _hnodup, ⟨base, hbaseSorted, _hbaseNodup, hrot⟩⟩
  rcases (List.isRotated_iff_mod).1 hrot with ⟨r, hrle, hrotate⟩

  -- lengths: base.length = nums.length
  have hlen_eq : base.length = nums.length :=
    (List.length_rotate base r).symm.trans (congrArg List.length hrotate)

  have hn_pos : 0 < base.length := by
    simpa [hlen_eq] using hlen_pos

  let n : Nat := base.length
  have hn_eq : n = nums.length := by simpa [n, hlen_eq]
  have hrle' : r ≤ n := by simpa [n] using hrle
  let p : Nat := n - r

  -- Strict monotonicity of base.get
  have hsm : StrictMono base.get := List.Sorted.get_strictMono hbaseSorted

  -- Element access through the rotation: (base.rotate r)[i] maps to base[(i+r)%n].
  have hnums_get_mod (i : Nat) (hi : i < nums.length) :
      nums[i]'hi = base[(i + r) % n]'(by
        have : 0 < n := by simpa [n] using hn_pos
        exact Nat.mod_lt _ this) := by
    have hi' : i < (base.rotate r).length := by simpa [hrotate] using hi
    simpa [hrotate, n] using (List.getElem_rotate (l := base) (n := r) (k := i) hi')

  -- helper: if n ≤ x and x < 2n then x - n < n
  have sub_lt_of_lt_two (x : Nat) (hx₁ : n ≤ x) (hx₂ : x < n + n) : x - n < n := by
    have ht : x - n + n < n + n := by
      simpa [Nat.sub_add_cancel hx₁, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx₂
    exact (Nat.add_lt_add_iff_right (k := n)).1 ht

  -- arithmetic helper: if n ≤ x < 2n then x % n = x - n
  have mod_eq_sub (x : Nat) (hx₁ : n ≤ x) (hx₂ : x < n + n) : x % n = x - n := by
    have hx_sub_lt : x - n < n := sub_lt_of_lt_two x hx₁ hx₂
    calc
      x % n = ((x - n) + n) % n := by simp [Nat.sub_add_cancel hx₁]
      _ = (((x - n) % n) + (n % n)) % n := by simpa [Nat.add_mod]
      _ = (x - n) % n := by simp
      _ = x - n := Nat.mod_eq_of_lt hx_sub_lt

  -- Main argument
  by_contra hknot
  have hmid_le_k : mid ≤ k := (not_lt).1 hknot

  -- Convert nat bounds to bounds over n.
  have hlo_n : lo < n := by simpa [hn_eq] using hlo_len
  have hmid_n : mid < n := by simpa [hn_eq] using hmid_len
  have hk_n : k < n := by simpa [hn_eq] using hk_len

  by_cases hlo_p : lo < p
  · -- lo in prefix
    have hmid_p : mid < p := by
      by_contra h
      have hp_le_mid : p ≤ mid := (not_lt).1 h
      have hlo_r_lt : lo + r < n := by
        have : lo + r < (n - r) + r := Nat.add_lt_add_right hlo_p r
        simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this
      have hn_le_mid_r : n ≤ mid + r := by
        have : (n - r) + r ≤ mid + r := Nat.add_le_add_right hp_le_mid r
        simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this
      have hmid_r_lt_2n : mid + r < n + n := by
        have h1 : mid + r < n + r := Nat.add_lt_add_right hmid_n r
        have h2 : n + r ≤ n + n := Nat.add_le_add_left hrle' n
        exact lt_of_lt_of_le h1 h2
      have hmod_mid : (mid + r) % n = mid + r - n := mod_eq_sub (mid + r) hn_le_mid_r hmid_r_lt_2n
      have hmod_lo : (lo + r) % n = lo + r := Nat.mod_eq_of_lt hlo_r_lt

      have hlo_repr : nums[lo]'hlo_len = base[lo + r]'(by simpa [n] using hlo_r_lt) := by
        simpa [n, hmod_lo] using hnums_get_mod lo hlo_len
      have hmid_repr : nums[mid]'hmid_len = base[mid + r - n]'(sub_lt_of_lt_two (mid + r) hn_le_mid_r hmid_r_lt_2n) := by
        simpa [n, hmod_mid] using hnums_get_mod mid hmid_len

      have hmididx_lt_r : mid + r - n < r := by
        have ht : mid + r - n + n < r + n := by
          have h1 : mid + r < n + r := Nat.add_lt_add_right hmid_n r
          -- rewrite left and right to match
          calc
            mid + r - n + n = mid + r := Nat.sub_add_cancel hn_le_mid_r
            _ < n + r := h1
            _ = r + n := by ac_rfl
        exact (Nat.add_lt_add_iff_right (k := n)).1 ht

      have hmididx_lt_loidx : mid + r - n < lo + r :=
        lt_of_lt_of_le hmididx_lt_r (Nat.le_add_left r lo)

      have hFin : (⟨mid + r - n, sub_lt_of_lt_two (mid + r) hn_le_mid_r hmid_r_lt_2n⟩ : Fin n)
          < ⟨lo + r, by simpa [n] using hlo_r_lt⟩ :=
        Fin.lt_iff_val_lt_val.2 hmididx_lt_loidx

      have hlt : nums[mid]'hmid_len < nums[lo]'hlo_len := by
        have := hsm hFin
        simpa [hlo_repr, hmid_repr] using this

      exact (not_lt_of_ge hlo_mid_le) hlt

    by_cases hk_p : k < p
    · -- k in prefix too
      have hmid_lt_k : mid < k := by
        refine lt_of_le_of_ne hmid_le_k ?_
        intro hEq
        have : nums[mid]'hmid_len = target := by simpa [hEq] using hk_val
        exact (hmid_ne_target this)

      have hmid_r_lt : mid + r < n := by
        have : mid + r < (n - r) + r := Nat.add_lt_add_right hmid_p r
        simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this
      have hk_r_lt : k + r < n := by
        have : k + r < (n - r) + r := Nat.add_lt_add_right hk_p r
        simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this

      have hmod_mid : (mid + r) % n = mid + r := Nat.mod_eq_of_lt hmid_r_lt
      have hmod_k : (k + r) % n = k + r := Nat.mod_eq_of_lt hk_r_lt

      have hmid_repr : nums[mid]'hmid_len = base[mid + r]'(by simpa [n] using hmid_r_lt) := by
        simpa [n, hmod_mid] using hnums_get_mod mid hmid_len
      have hk_repr : nums[k]'hk_len = base[k + r]'(by simpa [n] using hk_r_lt) := by
        simpa [n, hmod_k] using hnums_get_mod k hk_len

      have hFin : (⟨mid + r, by simpa [n] using hmid_r_lt⟩ : Fin n)
          < ⟨k + r, by simpa [n] using hk_r_lt⟩ :=
        Fin.lt_iff_val_lt_val.2 (Nat.add_lt_add_right hmid_lt_k r)

      have hlt : nums[mid]'hmid_len < nums[k]'hk_len := by
        have := hsm hFin
        simpa [hmid_repr, hk_repr] using this

      have : nums[mid]'hmid_len < target := by simpa [hk_val] using hlt
      exact (not_lt_of_ge (le_of_lt htarget_lt_mid)) this

    · -- k in suffix
      have hp_le_k : p ≤ k := (not_lt).1 hk_p

      have hlo_r_lt : lo + r < n := by
        have : lo + r < (n - r) + r := Nat.add_lt_add_right hlo_p r
        simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this
      have hn_le_k_r : n ≤ k + r := by
        have : (n - r) + r ≤ k + r := Nat.add_le_add_right hp_le_k r
        simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this
      have hk_r_lt_2n : k + r < n + n := by
        have h1 : k + r < n + r := Nat.add_lt_add_right hk_n r
        have h2 : n + r ≤ n + n := Nat.add_le_add_left hrle' n
        exact lt_of_lt_of_le h1 h2

      have hmod_k : (k + r) % n = k + r - n := mod_eq_sub (k + r) hn_le_k_r hk_r_lt_2n

      have hkidx_lt_r : k + r - n < r := by
        have ht : k + r - n + n < r + n := by
          have h1 : k + r < n + r := Nat.add_lt_add_right hk_n r
          calc
            k + r - n + n = k + r := Nat.sub_add_cancel hn_le_k_r
            _ < n + r := h1
            _ = r + n := by ac_rfl
        exact (Nat.add_lt_add_iff_right (k := n)).1 ht

      have hlo_repr : nums[lo]'hlo_len = base[lo + r]'(by simpa [n] using hlo_r_lt) := by
        have hmod_lo : (lo + r) % n = lo + r := Nat.mod_eq_of_lt hlo_r_lt
        simpa [n, hmod_lo] using hnums_get_mod lo hlo_len
      have hk_repr : nums[k]'hk_len = base[k + r - n]'(sub_lt_of_lt_two (k + r) hn_le_k_r hk_r_lt_2n) := by
        simpa [n, hmod_k] using hnums_get_mod k hk_len

      have hkidx_lt_loidx : k + r - n < lo + r :=
        lt_of_lt_of_le hkidx_lt_r (Nat.le_add_left r lo)

      have hFin : (⟨k + r - n, sub_lt_of_lt_two (k + r) hn_le_k_r hk_r_lt_2n⟩ : Fin n)
          < ⟨lo + r, by simpa [n] using hlo_r_lt⟩ :=
        Fin.lt_iff_val_lt_val.2 hkidx_lt_loidx

      have hlt : nums[k]'hk_len < nums[lo]'hlo_len := by
        have := hsm hFin
        simpa [hk_repr, hlo_repr] using this

      have hk_lt_target : nums[k]'hk_len < target := lt_of_lt_of_le hlt hlo_le_target
      exact lt_irrefl target (by simpa [hk_val] using hk_lt_target)

  · -- lo in suffix
    have hp_le_lo : p ≤ lo := (not_lt).1 hlo_p
    have hp_le_mid : p ≤ mid := le_trans hp_le_lo hmid_ge_lo
    have hp_le_k : p ≤ k := le_trans hp_le_mid hmid_le_k

    have hmid_lt_k : mid < k := by
      refine lt_of_le_of_ne hmid_le_k ?_
      intro hEq
      have : nums[mid]'hmid_len = target := by simpa [hEq] using hk_val
      exact (hmid_ne_target this)

    have hn_le_mid_r : n ≤ mid + r := by
      have : (n - r) + r ≤ mid + r := Nat.add_le_add_right hp_le_mid r
      simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this
    have hn_le_k_r : n ≤ k + r := by
      have : (n - r) + r ≤ k + r := Nat.add_le_add_right hp_le_k r
      simpa [p, Nat.sub_add_cancel hrle', Nat.add_assoc] using this

    have hmid_r_lt_2n : mid + r < n + n := by
      have h1 : mid + r < n + r := Nat.add_lt_add_right hmid_n r
      have h2 : n + r ≤ n + n := Nat.add_le_add_left hrle' n
      exact lt_of_lt_of_le h1 h2
    have hk_r_lt_2n : k + r < n + n := by
      have h1 : k + r < n + r := Nat.add_lt_add_right hk_n r
      have h2 : n + r ≤ n + n := Nat.add_le_add_left hrle' n
      exact lt_of_lt_of_le h1 h2

    have hmod_mid : (mid + r) % n = mid + r - n := mod_eq_sub (mid + r) hn_le_mid_r hmid_r_lt_2n
    have hmod_k : (k + r) % n = k + r - n := mod_eq_sub (k + r) hn_le_k_r hk_r_lt_2n

    have hmid_repr : nums[mid]'hmid_len = base[mid + r - n]'(sub_lt_of_lt_two (mid + r) hn_le_mid_r hmid_r_lt_2n) := by
      simpa [n, hmod_mid] using hnums_get_mod mid hmid_len

    have hk_repr : nums[k]'hk_len = base[k + r - n]'(sub_lt_of_lt_two (k + r) hn_le_k_r hk_r_lt_2n) := by
      simpa [n, hmod_k] using hnums_get_mod k hk_len

    have hidx_lt : mid + r - n < k + r - n := by
      have h1 : mid + r < k + r := Nat.add_lt_add_right hmid_lt_k r
      have h2 : mid + r - n + n < k + r - n + n := by
        calc
          mid + r - n + n = mid + r := Nat.sub_add_cancel hn_le_mid_r
          _ < k + r := h1
          _ = k + r - n + n := (Nat.sub_add_cancel hn_le_k_r).symm
      exact (Nat.add_lt_add_iff_right (k := n)).1 h2

    have hFin : (⟨mid + r - n, sub_lt_of_lt_two (mid + r) hn_le_mid_r hmid_r_lt_2n⟩ : Fin n)
        < ⟨k + r - n, sub_lt_of_lt_two (k + r) hn_le_k_r hk_r_lt_2n⟩ :=
      Fin.lt_iff_val_lt_val.2 hidx_lt

    have hlt : nums[mid]'hmid_len < nums[k]'hk_len := by
      have := hsm hFin
      simpa [hmid_repr, hk_repr] using this

    have : nums[mid]'hmid_len < target := by simpa [hk_val] using hlt
    exact (not_lt_of_ge (le_of_lt htarget_lt_mid)) this

theorem goal_1
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (a_1 : hi ≤ nums.length)
    (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target)
    (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target)
    (a_3 : target < nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < lo + (hi - lo) / OfNat.ofNat 2 ∧ nums[k]?.getD (OfNat.ofNat 0) = target := by
  intro hans hmem
  obtain ⟨k, hklo, hkhi, hkval⟩ := invariant_inv_search_space hans hmem
  have hkltmid : k < lo + (hi - lo) / 2 := by
    expose_names; exact (goal_1_0 nums target hi lo a if_pos require_1 a_1 if_neg if_pos_1 a_2 a_3 k hkhi hkval)
  exact ⟨k, hklo, hkltmid, hkval⟩

theorem goal_2_0
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (invariant_inv_found_forces_exit : ¬ans = -OfNat.ofNat 1 → lo = hi)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (a_1 : hi ≤ nums.length)
    (invariant_inv_len : True)
    (invariant_inv_ans_sound : ans = -OfNat.ofNat 1 ∨ ∃ i < nums.length, nums[i]? = some target ∧ ans = ↑i)
    (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target)
    (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target)
    (hans : ans = -OfNat.ofNat 1)
    (hmem : target ∈ nums)
    (hmid_lt_hi : lo + (hi - lo) / 2 < hi)
    : ∀ (k : ℕ),
  lo ≤ k →
    k ≤ lo + (hi - lo) / 2 → nums[lo]?.getD 0 ≤ nums[k]?.getD 0 ∧ nums[k]?.getD 0 ≤ nums[lo + (hi - lo) / 2]?.getD 0 := by
    sorry

theorem goal_2
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (invariant_inv_found_forces_exit : ¬ans = -OfNat.ofNat 1 → lo = hi)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (a_1 : hi ≤ nums.length)
    (invariant_inv_len : True)
    (invariant_inv_ans_sound : ans = -OfNat.ofNat 1 ∨ ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast)
    (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target)
    (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_pos_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0))
    (if_neg_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target)
    : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target := by
  intro hans hmem
  have hmid_lt_hi : lo + (hi - lo) / 2 < hi := by
    expose_names; intros; expose_names; try simp_all; try grind
  have hleft_bounds : ∀ k, lo ≤ k → k ≤ lo + (hi - lo) / 2 →
      nums[lo]?.getD 0 ≤ nums[k]?.getD 0 ∧ nums[k]?.getD 0 ≤ nums[lo + (hi - lo) / 2]?.getD 0 := by
    expose_names; exact (goal_2_0 nums target ans hi lo a invariant_inv_found_forces_exit if_pos require_1 a_1 invariant_inv_len invariant_inv_ans_sound invariant_inv_search_space if_neg if_pos_1 if_neg_1 hans hmem hmid_lt_hi)
  rcases invariant_inv_search_space hans hmem with ⟨k, hklo, hkhi, hkval⟩
  refine ⟨k, ?_, hkhi, hkval⟩
  by_contra hk
  have hk' : k ≤ lo + (hi - lo) / 2 := by
    -- from ¬(mid+1 ≤ k)
    have : k < lo + (hi - lo) / 2 + 1 := Nat.lt_of_not_ge hk
    exact Nat.le_of_lt_succ this
  have hb := hleft_bounds k hklo hk'
  have hlo_le_t : nums[lo]?.getD 0 ≤ target := by
    simpa [hkval] using hb.1
  have htarget_le_mid : target ≤ nums[lo + (hi - lo) / 2]?.getD 0 := by
    simpa [hkval] using hb.2
  have hmid_le_t : nums[lo + (hi - lo) / 2]?.getD 0 ≤ target := if_neg_1 hlo_le_t
  have hmid_eq_t : nums[lo + (hi - lo) / 2]?.getD 0 = target := le_antisymm hmid_le_t htarget_le_mid
  exact if_neg (by simpa [hmid_eq_t])

theorem goal_3
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (a_1 : hi ≤ nums.length)
    (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target)
    (if_neg_1 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0))
    (a_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target)
    (a_3 : target ≤ nums[hi - OfNat.ofNat 1]?.getD (OfNat.ofNat 0))
    : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1 ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target := by
  intro hans hmem
  obtain ⟨k, hklo, hkhi, hkval⟩ := invariant_inv_search_space hans hmem

  rcases require_1 with ⟨hlen_pos, hnodupNums, base, hsorted, hnodupBase, hrot⟩
  rcases hrot with ⟨r, hr⟩

  let n : Nat := base.length
  have hlen_nums : nums.length = n := by
    simpa [n, hr] using (List.length_rotate base r)
  have npos : 0 < n := by
    simpa [hlen_nums] using hlen_pos

  -- midpoint
  let mid : Nat := lo + (hi - lo) / 2

  -- basic bounds
  have hlo_lt_len : lo < nums.length := lt_of_lt_of_le if_pos a_1
  have hlo_lt_n : lo < n := by simpa [hlen_nums] using hlo_lt_len

  have hk_lt_len : k < nums.length := lt_of_lt_of_le hkhi a_1
  have hk_lt_n : k < n := by simpa [hlen_nums] using hk_lt_len

  have hmid_lt_hi : mid < hi := by
    have hsubpos : 0 < hi - lo := Nat.sub_pos_of_lt if_pos
    have hdiv : (hi - lo) / 2 < hi - lo := by
      simpa using (Nat.div_lt_self hsubpos (by decide : 1 < (2:Nat)))
    have : lo + (hi - lo) / 2 < lo + (hi - lo) := Nat.add_lt_add_left hdiv lo
    simpa [mid, Nat.add_sub_of_le a] using this

  have hmid_lt_len : mid < nums.length := lt_of_lt_of_le hmid_lt_hi a_1
  have hmid_lt_n : mid < n := by simpa [hlen_nums] using hmid_lt_len

  have hmid_ge_lo : lo ≤ mid := by simp [mid]
  have hlo_lt_mid : lo < mid := by
    have hne : mid ≠ lo := by
      intro hEq
      have hEq' : lo + (hi - lo) / 2 = lo := by simpa [mid] using hEq
      have : nums[lo]?.getD (0:ℤ) < nums[lo]?.getD (0:ℤ) := by
        simpa [hEq'] using if_neg_1
      exact (lt_irrefl _ this)
    exact lt_of_le_of_ne hmid_ge_lo (Ne.symm hne)

  -- StrictMono for base.get
  have hstrict : StrictMono base.get := List.Sorted.get_strictMono hsorted

  -- rotate index uses r mod n
  let r' : Nat := r % n
  have hr'lt : r' < n := Nat.mod_lt _ npos

  have hmod (i : Nat) (hi : i < n) : (i + r) % n = (i + r') % n := by
    have : i % n = i := Nat.mod_eq_of_lt hi
    simp [r', Nat.add_mod, this, Nat.mod_mod]

  -- value interpretation through rotation
  let val (i : Nat) : ℤ := (nums.get? i).getD 0

  have hval (i : Nat) (hi : i < n) : val i = base.get ⟨(i + r') % n, Nat.mod_lt _ npos⟩ := by
    -- first, val i = nums.get ⟨i, _⟩
    have hv1 : val i = nums.get ⟨i, by simpa [hlen_nums] using hi⟩ := by
      simp [val, List.get?, hi, hlen_nums]
    -- use get_rotate on base
    have hiRot : i < (base.rotate r).length := by
      simpa [List.length_rotate, n] using hi
    have hv2 : (base.rotate r).get ⟨i, hiRot⟩ = base.get ⟨(i + r) % n, Nat.mod_lt _ npos⟩ := by
      simpa [n] using (List.get_rotate (l := base) (n := r) (k := ⟨i, hiRot⟩))
    have hv3 : nums.get ⟨i, by simpa [hlen_nums] using hi⟩ = base.get ⟨(i + r) % n, Nat.mod_lt _ npos⟩ := by
      simpa [hr] using hv2
    have hidx : (i + r) % n = (i + r') % n := hmod i hi
    have hfin : (⟨(i + r) % n, Nat.mod_lt _ npos⟩ : Fin n) = ⟨(i + r') % n, Nat.mod_lt _ npos⟩ := by
      apply Fin.ext; exact hidx
    calc
      val i = nums.get ⟨i, by simpa [hlen_nums] using hi⟩ := hv1
      _ = base.get ⟨(i + r) % n, Nat.mod_lt _ npos⟩ := hv3
      _ = base.get ⟨(i + r') % n, Nat.mod_lt _ npos⟩ := by simpa [hfin]

  have hloVal : val lo = base.get ⟨(lo + r') % n, Nat.mod_lt _ npos⟩ := hval lo hlo_lt_n
  have hmidVal : val mid = base.get ⟨(mid + r') % n, Nat.mod_lt _ npos⟩ := hval mid hmid_lt_n

  -- from midVal < loVal infer index order
  have hidx_mid_lt_lo : (⟨(mid + r') % n, Nat.mod_lt _ npos⟩ : Fin n) < ⟨(lo + r') % n, Nat.mod_lt _ npos⟩ := by
    have : base.get ⟨(mid + r') % n, Nat.mod_lt _ npos⟩ < base.get ⟨(lo + r') % n, Nat.mod_lt _ npos⟩ := by
      have : val mid < val lo := by
        simpa [val, mid] using if_neg_1
      simpa [hmidVal, hloVal] using this
    exact (hstrict.lt_iff_lt).1 this
  have hidx_mid_lt_lo_nat : ((mid + r') % n) < ((lo + r') % n) := by simpa using hidx_mid_lt_lo

  -- show lo+r' < n
  have hlo_add_lt : lo + r' < n := by
    by_contra hge
    have hlo_add_ge : n ≤ lo + r' := Nat.le_of_not_gt hge
    have hmid_add_ge : n ≤ mid + r' := by
      have : lo + r' ≤ mid + r' := Nat.add_le_add_right hmid_ge_lo r'
      exact hlo_add_ge.trans this
    -- in this wrapped case, modulo is (x+r')-n
    have hmod_lo : (lo + r') % n = lo + r' - n := by
      have hsub_lt : lo + r' - n < n := by omega
      calc
        (lo + r') % n = (lo + r' - n) % n := Nat.mod_eq_sub_mod hlo_add_ge
        _ = lo + r' - n := Nat.mod_eq_of_lt hsub_lt
    have hmod_mid : (mid + r') % n = mid + r' - n := by
      have hsub_lt : mid + r' - n < n := by omega
      calc
        (mid + r') % n = (mid + r' - n) % n := Nat.mod_eq_sub_mod hmid_add_ge
        _ = mid + r' - n := Nat.mod_eq_of_lt hsub_lt
    have : (lo + r') % n < (mid + r') % n := by
      have : lo + r' - n < mid + r' - n := by omega
      simpa [hmod_lo, hmod_mid] using this
    exact (not_lt_of_ge (Nat.le_of_lt hidx_mid_lt_lo_nat)) this

  -- show mid+r' ≥ n
  have hmid_add_ge : n ≤ mid + r' := by
    by_contra hlt
    have hmid_add_lt : mid + r' < n := Nat.lt_of_not_ge hlt
    have hmod_mid : (mid + r') % n = mid + r' := Nat.mod_eq_of_lt hmid_add_lt
    have hmod_lo : (lo + r') % n = lo + r' := Nat.mod_eq_of_lt hlo_add_lt
    have : (lo + r') % n < (mid + r') % n := by
      have : lo + r' < mid + r' := Nat.add_lt_add_right hlo_lt_mid r'
      simpa [hmod_lo, hmod_mid] using this
    exact (not_lt_of_ge (Nat.le_of_lt hidx_mid_lt_lo_nat)) this

  -- bounds for hi-1
  have hhi_pos : 0 < hi := Nat.lt_of_le_of_lt (Nat.zero_le lo) if_pos
  have hhi1_lt_len : hi - 1 < nums.length := by
    have : hi - 1 < hi := Nat.sub_lt_self (by decide : 0 < 1) hhi_pos
    exact lt_of_lt_of_le this a_1
  have hhi1_lt_n : hi - 1 < n := by simpa [hlen_nums] using hhi1_lt_len
  have hmid_le_hi1 : mid ≤ hi - 1 := Nat.le_pred_of_lt hmid_lt_hi

  have hhi1_add_ge : n ≤ (hi - 1) + r' := by
    have : mid + r' ≤ (hi - 1) + r' := Nat.add_le_add_right hmid_le_hi1 r'
    exact hmid_add_ge.trans this

  -- hiVal < loVal
  have hhiVal_lt_loVal : val (hi - 1) < val lo := by
    have hmod_hi1 : ((hi - 1) + r') % n = (hi - 1) + r' - n := by
      have hsub_lt : (hi - 1) + r' - n < n := by omega
      calc
        ((hi - 1) + r') % n = (((hi - 1) + r') - n) % n := Nat.mod_eq_sub_mod hhi1_add_ge
        _ = (hi - 1) + r' - n := Nat.mod_eq_of_lt hsub_lt
    have hmod_lo : (lo + r') % n = lo + r' := Nat.mod_eq_of_lt hlo_add_lt
    have hidx_hi1_lt_lo : ((hi - 1) + r') % n < (lo + r') % n := by
      have : (hi - 1) + r' - n < lo + r' := by omega
      simpa [hmod_hi1, hmod_lo] using this
    have hfin : (⟨((hi - 1) + r') % n, Nat.mod_lt _ npos⟩ : Fin n) < ⟨(lo + r') % n, Nat.mod_lt _ npos⟩ := by
      simpa using hidx_hi1_lt_lo
    have : base.get ⟨((hi - 1) + r') % n, Nat.mod_lt _ npos⟩ < base.get ⟨(lo + r') % n, Nat.mod_lt _ npos⟩ :=
      hstrict hfin
    have hhi1Val : val (hi - 1) = base.get ⟨((hi - 1) + r') % n, Nat.mod_lt _ npos⟩ := hval (hi - 1) hhi1_lt_n
    simpa [hhi1Val, hloVal] using this

  have htarget_lt_lo : target < val lo := by
    have : target ≤ val (hi - 1) := by
      simpa [val] using a_3
    exact lt_of_le_of_lt this hhiVal_lt_loVal

  -- Now show k > mid
  have hk_mid_lt : mid < k := by
    by_contra hk_le
    have hk_le_mid : k ≤ mid := Nat.le_of_not_gt hk_le

    have hkVal : val k = base.get ⟨(k + r') % n, Nat.mod_lt _ npos⟩ := hval k hk_lt_n

    by_cases hk_add_lt : k + r' < n
    · -- nonwrapped: val lo ≤ val k
      have hmod_k : (k + r') % n = k + r' := Nat.mod_eq_of_lt hk_add_lt
      have hmod_lo : (lo + r') % n = lo + r' := Nat.mod_eq_of_lt hlo_add_lt
      have hfin_le : (⟨(lo + r') % n, Nat.mod_lt _ npos⟩ : Fin n) ≤ ⟨(k + r') % n, Nat.mod_lt _ npos⟩ := by
        have : lo + r' ≤ k + r' := Nat.add_le_add_right hklo r'
        simpa [hmod_lo, hmod_k] using this
      have hlo_le_hk : val lo ≤ val k := by
        have : base.get ⟨(lo + r') % n, Nat.mod_lt _ npos⟩ ≤ base.get ⟨(k + r') % n, Nat.mod_lt _ npos⟩ :=
          (hstrict.monotone) hfin_le
        simpa [hloVal, hkVal] using this
      have : val k < val lo := by
        -- val k = target
        have : target < val lo := htarget_lt_lo
        simpa [val, hkval] using this
      exact (not_lt_of_ge hlo_le_hk) this

    · -- wrapped: val k < target
      have hk_add_ge : n ≤ k + r' := Nat.le_of_not_gt hk_add_lt
      have hmod_k : (k + r') % n = k + r' - n := by
        have hsub_lt : k + r' - n < n := by omega
        calc
          (k + r') % n = (k + r' - n) % n := Nat.mod_eq_sub_mod hk_add_ge
          _ = k + r' - n := Nat.mod_eq_of_lt hsub_lt
      have hmod_mid : (mid + r') % n = mid + r' - n := by
        have hsub_lt : mid + r' - n < n := by omega
        calc
          (mid + r') % n = (mid + r' - n) % n := Nat.mod_eq_sub_mod hmid_add_ge
          _ = mid + r' - n := Nat.mod_eq_of_lt hsub_lt
      have hfin_le : (⟨(k + r') % n, Nat.mod_lt _ npos⟩ : Fin n) ≤ ⟨(mid + r') % n, Nat.mod_lt _ npos⟩ := by
        have : k + r' - n ≤ mid + r' - n := by
          exact Nat.sub_le_sub_right (Nat.add_le_add_right hk_le_mid r') n
        simpa [hmod_k, hmod_mid] using this
      have hk_le_midVal : val k ≤ val mid := by
        have : base.get ⟨(k + r') % n, Nat.mod_lt _ npos⟩ ≤ base.get ⟨(mid + r') % n, Nat.mod_lt _ npos⟩ :=
          (hstrict.monotone) hfin_le
        simpa [hkVal, hmidVal] using this
      have hmid_lt_target : val mid < target := by
        simpa [val, mid] using a_2
      have hk_lt_target : val k < target := lt_of_le_of_lt hk_le_midVal hmid_lt_target
      have : target < target := by
        simpa [val, hkval] using hk_lt_target
      exact (lt_irrefl target this)

  have hk_succ : mid + 1 ≤ k := (Nat.succ_le_iff).2 hk_mid_lt
  refine ⟨k, ?_, hkhi, hkval⟩
  simpa [mid, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk_succ



theorem goal_4
    (nums : List ℤ)
    (target : ℤ)
    (ans : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (invariant_inv_found_forces_exit : ¬ans = -OfNat.ofNat 1 → lo = hi)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (a_1 : hi ≤ nums.length)
    (invariant_inv_len : True)
    (invariant_inv_ans_sound : ans = -OfNat.ofNat 1 ∨ ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast)
    (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target)
    (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target)
    (if_neg_1 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0))
    (if_neg_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target → nums[hi - OfNat.ofNat 1]?.getD (OfNat.ofNat 0) < target)
    : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < lo + (hi - lo) / OfNat.ofNat 2 ∧ nums[k]?.getD (OfNat.ofNat 0) = target := by
    sorry

theorem goal_5
    (nums : List ℤ)
    (target : ℤ)
    (i : ℤ)
    (i_1 : ℕ)
    (lo_1 : ℕ)
    (a : lo_1 ≤ i_1)
    (invariant_inv_found_forces_exit : ¬i = -OfNat.ofNat 1 → lo_1 = i_1)
    (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums)
    (invariant_inv_len : True)
    (invariant_inv_ans_sound : i = -OfNat.ofNat 1 ∨ ∃ i_2 < nums.length, nums[i_2]? = some target ∧ i = i_2.cast)
    (a_1 : i_1 ≤ nums.length)
    (done_1 : i_1 ≤ lo_1)
    (invariant_inv_search_space : i = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo_1 ≤ k ∧ k < i_1 ∧ nums[k]?.getD (OfNat.ofNat 0) = target)
    : postcondition nums target i := by
    sorry



prove_correct SearchInRotatedSortedArray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums hi lo if_pos a_1)
  exact (goal_1 nums target ans hi lo a if_pos require_1 a_1 invariant_inv_search_space if_neg if_pos_1 a_2 a_3)
  exact (goal_2 nums target ans hi lo a invariant_inv_found_forces_exit if_pos require_1 a_1 invariant_inv_len invariant_inv_ans_sound invariant_inv_search_space if_neg if_pos_1 if_neg_1)
  exact (goal_3 nums target ans hi lo a if_pos require_1 a_1 invariant_inv_search_space if_neg_1 a_2 a_3)
  exact (goal_4 nums target ans hi lo a invariant_inv_found_forces_exit if_pos require_1 a_1 invariant_inv_len invariant_inv_ans_sound invariant_inv_search_space if_neg if_neg_1 if_neg_2)
  exact (goal_5 nums target i i_1 lo_1 a invariant_inv_found_forces_exit require_1 invariant_inv_len invariant_inv_ans_sound a_1 done_1 invariant_inv_search_space)
end Proof
