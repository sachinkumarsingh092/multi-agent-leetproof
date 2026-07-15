import Mathlib.Tactic

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

/-! ## Helper lemmas -/
section HelperLemmas

set_option maxHeartbeats 40000000

private lemma pairwise_lt_monotone' (base : List ℤ) (i j : ℕ)
    (hsorted : base.Pairwise (· < ·))
    (hi : i < base.length) (hj : j < base.length) (hij : i ≤ j) :
    base[i]?.getD 0 ≤ base[j]?.getD 0 := by
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_refl _
  · rw [List.pairwise_iff_get] at hsorted
    simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
    exact le_of_lt (hsorted ⟨i, hi⟩ ⟨j, hj⟩ hlt)

private lemma pairwise_lt_strict' (base : List ℤ) (i j : ℕ)
    (hsorted : base.Pairwise (· < ·))
    (hi : i < base.length) (hj : j < base.length) (hij : i < j) :
    base[i]?.getD 0 < base[j]?.getD 0 := by
  rw [List.pairwise_iff_get] at hsorted
  simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
  exact hsorted ⟨i, hi⟩ ⟨j, hj⟩ hij

private lemma rotate_getD (nums base : List ℤ) (r p : ℕ)
    (hr : nums = base.rotate r) (hp : p < base.length) :
    nums[p]?.getD 0 = base[(p + r) % base.length]?.getD 0 := by
  subst hr; rw [List.getElem?_rotate]; simp [hp]

private lemma rotate_getD' (nums base : List ℤ) (r p : ℕ)
    (hr : base.rotate r = nums) (hp : p < base.length) :
    nums[p]?.getD 0 = base[(p + r) % base.length]?.getD 0 :=
  rotate_getD nums base r p hr.symm hp

-- Helper for upper bound in quotient calculations
private lemma upper_bound_calc (lo r n q : ℕ) (hq1 : lo + r < q * n)
    (hi_val : ℕ) (hhi : hi_val ≤ n) : hi_val - 1 + r < (q + 1) * n := by
  have : r < q * n := by omega
  calc hi_val - 1 + r ≤ n - 1 + r := by omega
    _ < n + q * n := by omega
    _ = (q + 1) * n := by ring

end HelperLemmas

section Proof

set_option maxHeartbeats 40000000

theorem goal_2_0 (nums : List ℤ) (target : ℤ) (ans : ℤ) (hi : ℕ) (lo : ℕ) (a : lo ≤ hi) (invariant_inv_found_forces_exit : ¬ans = -OfNat.ofNat 1 → lo = hi) (if_pos : lo < hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (a_1 : hi ≤ nums.length) (invariant_inv_len : True) (invariant_inv_ans_sound : ans = -OfNat.ofNat 1 ∨ ∃ i < nums.length, nums[i]? = some target ∧ ans = ↑i) (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target) (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_pos_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0)) (if_neg_1 : nums[lo]?.getD (OfNat.ofNat 0) ≤ target → nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) ≤ target) (hans : ans = -OfNat.ofNat 1) (hmem : target ∈ nums) (hmid_lt_hi : lo + (hi - lo) / 2 < hi) : ∀ (k : ℕ),
  lo ≤ k →
    k ≤ lo + (hi - lo) / 2 → nums[lo]?.getD 0 ≤ nums[k]?.getD 0 ∧ nums[k]?.getD 0 ≤ nums[lo + (hi - lo) / 2]?.getD 0 := by
    intro k hlo_le_k hk_le_mid
    set mid := lo + (hi - lo) / 2 with hmid_def
    obtain ⟨_, hnodup, base, hbase_sorted, _, hbase_rot⟩ := require_1
    obtain ⟨r, hr⟩ : ∃ r, nums = base.rotate r := by cases hbase_rot; rename_i n _; exact ⟨n, by aesop⟩
    have hn_eq : base.length = nums.length := by rw [hr, List.length_rotate]
    have hn_pos : base.length > 0 := by omega
    have h_get : ∀ p, p < nums.length → nums[p]?.getD 0 = base[(p + r) % base.length]?.getD 0 :=
      fun p hp => rotate_getD nums base r p hr (by omega)
    -- (lo+r)%n ≤ (mid+r)%n from if_pos_1
    have h_lo_mid_mod : (lo + r) % base.length ≤ (mid + r) % base.length := by
      by_contra h_contra; push_neg at h_contra
      have h1 := pairwise_lt_strict' base _ _ hbase_sorted
        (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) h_contra
      rw [← h_get lo (by omega), ← h_get mid (by omega)] at h1
      linarith
    -- Quotients are equal
    have h_div_eq : (lo + r) / base.length = (mid + r) / base.length := by
      by_contra h_contra
      have h_lt : (lo + r) / base.length < (mid + r) / base.length :=
        lt_of_le_of_ne (Nat.div_le_div_right (by omega)) h_contra
      nlinarith [Nat.mod_add_div (lo + r) base.length, Nat.mod_add_div (mid + r) base.length,
        Nat.zero_le ((lo + r) % base.length), Nat.zero_le ((mid + r) % base.length),
        Nat.mod_lt (lo + r) hn_pos, Nat.mod_lt (mid + r) hn_pos]
    -- k's quotient is the same
    have h_k_div : (k + r) / base.length = (lo + r) / base.length := by
      apply le_antisymm
      · calc (k + r) / base.length ≤ (mid + r) / base.length := Nat.div_le_div_right (by omega)
          _ = _ := h_div_eq.symm
      · exact Nat.div_le_div_right (by omega)
    -- Mods preserve order
    have h_lo_k_mod : (lo + r) % base.length ≤ (k + r) % base.length := by
      nlinarith [Nat.mod_add_div (lo + r) base.length, Nat.mod_add_div (k + r) base.length]
    have h_k_mid_mod : (k + r) % base.length ≤ (mid + r) % base.length := by
      have h_k_div2 : (k + r) / base.length = (mid + r) / base.length := by
        rw [h_k_div, h_div_eq]
      nlinarith [Nat.mod_add_div (k + r) base.length, Nat.mod_add_div (mid + r) base.length]
    constructor
    · rw [h_get lo (by omega), h_get k (by omega)]
      exact pairwise_lt_monotone' base _ _ hbase_sorted (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) h_lo_k_mod
    · rw [h_get k (by omega), h_get mid (by omega)]
      exact pairwise_lt_monotone' base _ _ hbase_sorted (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) h_k_mid_mod

theorem goal_4 (nums : List ℤ) (target : ℤ) (ans : ℤ) (hi : ℕ) (lo : ℕ) (a : lo ≤ hi) (invariant_inv_found_forces_exit : ¬ans = -OfNat.ofNat 1 → lo = hi) (if_pos : lo < hi) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (a_1 : hi ≤ nums.length) (invariant_inv_len : True) (invariant_inv_ans_sound : ans = -OfNat.ofNat 1 ∨ ∃ i < nums.length, nums[i]? = some target ∧ ans = i.cast) (invariant_inv_search_space : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < hi ∧ nums[k]?.getD (OfNat.ofNat 0) = target) (if_neg : ¬nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) = target) (if_neg_1 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < nums[lo]?.getD (OfNat.ofNat 0)) (if_neg_2 : nums[lo + (hi - lo) / OfNat.ofNat 2]?.getD (OfNat.ofNat 0) < target → nums[hi - OfNat.ofNat 1]?.getD (OfNat.ofNat 0) < target) : ans = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo ≤ k ∧ k < lo + (hi - lo) / OfNat.ofNat 2 ∧ nums[k]?.getD (OfNat.ofNat 0) = target := by
    intro hans hmem
    set mid := lo + (hi - lo) / 2 with hmid_def
    obtain ⟨_, hnodup, base, hbase_sorted, _, hbase_rot⟩ := require_1
    obtain ⟨kk, hkk_lo, hkk_hi, hkk_eq⟩ := invariant_inv_search_space hans hmem
    by_contra h_not; push_neg at h_not
    have hkk_ge_mid : mid ≤ kk := by
      by_contra hlt; push_neg at hlt; exact h_not kk hkk_lo hlt hkk_eq
    have hkk_ne_mid : kk ≠ mid := fun h => if_neg (h ▸ hkk_eq)
    have hkk_gt_mid : mid < kk := by omega
    obtain ⟨r, hr⟩ : ∃ r, base.rotate r = nums := hbase_rot
    have hn_eq : base.length = nums.length := by rw [← hr, List.length_rotate]
    have hn_pos : base.length > 0 := by omega
    have h_get : ∀ p, p < base.length → nums[p]?.getD 0 = base[(p + r) % base.length]?.getD 0 :=
      fun p hp => rotate_getD' nums base r p hr hp
    -- (mid+r)%n < (lo+r)%n
    have h_mod_lt : (mid + r) % base.length < (lo + r) % base.length := by
      by_contra h_contra; push_neg at h_contra
      have := pairwise_lt_monotone' base _ _ hbase_sorted (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) h_contra
      rw [← h_get lo (by omega), ← h_get mid (by omega)] at this
      linarith
    -- Wrap-around
    have hlo_le_mid : lo ≤ mid := by omega
    obtain ⟨q, hq1, hq2⟩ : ∃ q, lo + r < q * base.length ∧ q * base.length ≤ mid + r := by
      have : (mid + r) / base.length ≥ (lo + r) / base.length + 1 := by
        by_contra h_le
        push_neg at h_le
        -- (mid+r)/n ≤ (lo+r)/n, but mid+r ≥ lo+r and (mid+r)%n < (lo+r)%n
        have hle_div : (mid + r) / base.length ≤ (lo + r) / base.length := by omega
        have h1 := Nat.mod_add_div (mid + r) base.length
        have h2 := Nat.mod_add_div (lo + r) base.length
        -- mid+r ≥ lo+r
        have : lo + r ≤ mid + r := by omega
        -- n * (mid+r)/n + (mid+r)%n ≥ n * (lo+r)/n + (lo+r)%n
        -- n * (mid+r)/n ≤ n * (lo+r)/n (from hle_div)
        -- So (mid+r)%n ≥ (lo+r)%n, contradicting h_mod_lt
        have : base.length * ((mid + r) / base.length) ≤ base.length * ((lo + r) / base.length) :=
          Nat.mul_le_mul_left _ hle_div
        nlinarith
      exact ⟨(lo + r) / base.length + 1,
        by nlinarith [Nat.div_add_mod (lo + r) base.length, Nat.mod_lt (lo + r) hn_pos],
        by nlinarith [Nat.div_mul_le_self (mid + r) base.length]⟩
    -- Upper bound for all indices in [mid, hi-1]
    have h_upper : ∀ p, p ≤ hi - 1 → p + r < (q + 1) * base.length := by
      intro p hp
      have : r < q * base.length := by omega
      calc p + r ≤ hi - 1 + r := by omega
        _ ≤ base.length - 1 + r := by omega
        _ < base.length + q * base.length := by omega
        _ = (q + 1) * base.length := by ring
    -- All indices from mid to hi-1 have quotient q
    have h_mid_div : (mid + r) / base.length = q :=
      Nat.div_eq_of_lt_le (by omega) (h_upper mid (by omega))
    have h_kk_div : (kk + r) / base.length = q :=
      Nat.div_eq_of_lt_le (by omega) (h_upper kk (by omega))
    have h_hi1_div : (hi - 1 + r) / base.length = q :=
      Nat.div_eq_of_lt_le (by omega) (h_upper (hi - 1) (by omega))
    -- mid < kk ⟹ (mid+r)%n < (kk+r)%n
    have h_mid_kk_mod : (mid + r) % base.length < (kk + r) % base.length := by
      nlinarith [Nat.mod_add_div (mid + r) base.length, Nat.mod_add_div (kk + r) base.length]
    -- kk ≤ hi-1 ⟹ (kk+r)%n ≤ (hi-1+r)%n
    have hkk_le_hi1_nat : kk ≤ hi - 1 := by omega
    have h_kk_hi1_mod : (kk + r) % base.length ≤ (hi - 1 + r) % base.length := by
      have h1 := Nat.mod_add_div (kk + r) base.length
      have h2 := Nat.mod_add_div (hi - 1 + r) base.length
      have : kk + r ≤ hi - 1 + r := by omega
      nlinarith
    -- nums[mid] < nums[kk]
    have hmid_lt_kk : nums[mid]?.getD 0 < nums[kk]?.getD 0 := by
      rw [h_get mid (by omega), h_get kk (by omega)]
      exact pairwise_lt_strict' base _ _ hbase_sorted (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) h_mid_kk_mod
    -- nums[mid] < target
    have hkk_val : nums[kk]?.getD (0 : ℤ) = target := hkk_eq
    have hmid_lt_target : nums[mid]?.getD 0 < target := by linarith
    -- nums[hi-1] < target
    have hhi1_lt : nums[hi - 1]?.getD 0 < target := if_neg_2 hmid_lt_target
    -- nums[kk] ≤ nums[hi-1]
    have hkk_le_hi1 : nums[kk]?.getD 0 ≤ nums[hi - 1]?.getD 0 := by
      rw [h_get kk (by omega), h_get (hi - 1) (by omega)]
      exact pairwise_lt_monotone' base _ _ hbase_sorted (Nat.mod_lt _ hn_pos) (Nat.mod_lt _ hn_pos) h_kk_hi1_mod
    -- target = nums[kk] ≤ nums[hi-1] < target: contradiction
    have hkk_val2 : nums[kk]?.getD (0 : ℤ) = target := hkk_eq
    linarith

theorem goal_5 (nums : List ℤ) (target : ℤ) (i : ℤ) (i_1 : ℕ) (lo_1 : ℕ) (a : lo_1 ≤ i_1) (invariant_inv_found_forces_exit : ¬i = -OfNat.ofNat 1 → lo_1 = i_1) (require_1 : OfNat.ofNat 0 < nums.length ∧ nums.Nodup ∧ ∃ base, List.Sorted (fun x1 x2 => x1 < x2) base ∧ base.Nodup ∧ base ~r nums) (invariant_inv_len : True) (invariant_inv_ans_sound : i = -OfNat.ofNat 1 ∨ ∃ i_2 < nums.length, nums[i_2]? = some target ∧ i = i_2.cast) (a_1 : i_1 ≤ nums.length) (done_1 : i_1 ≤ lo_1) (invariant_inv_search_space : i = -OfNat.ofNat 1 → target ∈ nums → ∃ k, lo_1 ≤ k ∧ k < i_1 ∧ nums[k]?.getD (OfNat.ofNat 0) = target) : postcondition nums target i := by
    unfold postcondition inList
    have hnodup := require_1.2.1
    rcases invariant_inv_ans_sound with h_neg | ⟨idx, hidx_lt, hidx_eq, hidx_cast⟩
    · -- i = -1: target ∉ nums
      left; constructor
      · exact h_neg
      · intro hmem
        obtain ⟨k, hk1, hk2, _⟩ := invariant_inv_search_space h_neg hmem
        omega
    · -- Found target at idx
      right
      have h_inj := List.nodup_iff_injective_getElem.mp hnodup
      refine ⟨idx, hidx_lt, ?_, hidx_cast, ?_⟩
      · -- nums.get? idx = some target
        rw [List.get?_eq_getElem?]; exact hidx_eq
      · -- Uniqueness
        intro j hj hj_eq
        rw [List.get?_eq_getElem?] at hj_eq
        have hj_val : nums[j]'hj = target := by
          rw [List.getElem?_eq_getElem hj] at hj_eq
          exact Option.some_injective _ hj_eq
        have hidx_val : nums[idx]'hidx_lt = target := by
          rw [List.getElem?_eq_getElem hidx_lt] at hidx_eq
          exact Option.some_injective _ hidx_eq
        have heq : (⟨j, hj⟩ : Fin nums.length) = ⟨idx, hidx_lt⟩ := by
          apply h_inj; simp only; rw [hj_val, hidx_val]
        exact Fin.val_eq_of_eq heq
end Proof
