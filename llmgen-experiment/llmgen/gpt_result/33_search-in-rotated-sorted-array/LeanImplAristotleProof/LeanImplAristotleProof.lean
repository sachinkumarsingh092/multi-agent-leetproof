import Lean

import Mathlib.Tactic
import Proof2

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
  nums.Pairwise (· < ·)

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

section HelperLemmas
set_option maxHeartbeats 800000

-- Top-level binary search equivalent to implementation.bs
def myBsImpl (target : ℤ) (arr : Array ℤ) (lo hi : Nat) : ℤ :=
  if h : lo < hi then
    let mid : Nat := lo + (hi - lo) / 2
    let midVal : ℤ := arr[mid]!
    if midVal = target then Int.ofNat mid
    else
      let loVal : ℤ := arr[lo]!
      if loVal ≤ midVal then
        if loVal ≤ target ∧ target < midVal then myBsImpl target arr lo mid
        else myBsImpl target arr (mid + 1) hi
      else
        let hiVal : ℤ := arr[hi - 1]!
        if midVal < target ∧ target ≤ hiVal then myBsImpl target arr (mid + 1) hi
        else myBsImpl target arr lo mid
  else (-1)
termination_by hi - lo

lemma myBsImpl_finds_target (target : ℤ) (arr : Array ℤ) (lo hi : Nat) (k : Nat) :
    myBsImpl target arr lo hi = Int.ofNat k → arr[k]! = target := by
  revert k; intro k hk
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi k
  unfold myBsImpl at hk; grind

set_option maxHeartbeats 1600000 in
lemma myBsImpl_range (target : ℤ) (arr : Array ℤ) (lo hi : Nat) (k : Nat) :
    myBsImpl target arr lo hi = Int.ofNat k → lo ≤ k ∧ k < hi := by
  intro h_eq_k
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi k
  unfold myBsImpl at h_eq_k
  split_ifs at h_eq_k ; norm_num at h_eq_k
  split_ifs at h_eq_k <;> norm_cast at *
  · omega
  · specialize ih (lo + (hi - lo) / 2 - lo) ?_ lo (lo + (hi - lo) / 2) k h_eq_k ?_ <;> norm_num at * <;> omega
  · specialize ih (hi - (lo + (hi - lo) / 2 + 1)) ?_ (lo + (hi - lo) / 2 + 1) hi k h_eq_k ?_ <;> omega
  · grind
  · specialize ih (lo + (hi - lo) / 2 - lo) ?_ lo (lo + (hi - lo) / 2) k h_eq_k rfl <;> norm_num at * <;> first | grind | omega

lemma bs_eq_myBsImpl (target : ℤ) (arr : Array ℤ) (lo hi : Nat) :
    implementation.bs target arr lo hi = myBsImpl target arr lo hi := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi
  unfold implementation.bs myBsImpl; split_ifs <;> norm_num at *
  rw [ih _ _ _ _ rfl, ih _ _ _ _ rfl] <;> omega

lemma impl_unfold' (nums : List ℤ) (target : ℤ) :
    implementation nums target = implementation.bs target nums.toArray 0 nums.toArray.size := rfl

-- myBsImpl = myBs2 (from Proof2)
set_option maxHeartbeats 800000 in
lemma myBsImpl_eq_myBs2 (target : ℤ) (arr : Array ℤ) (lo hi : Nat) :
    myBsImpl target arr lo hi = myBs2 target arr lo hi := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi
  unfold myBsImpl myBs2; split_ifs <;> norm_num at *
  rw [ih _ _ _ _ rfl, ih _ _ _ _ rfl] <;> omega

-- Completeness: myBsImpl finds target in rot_sorted nodup sub-array
set_option maxHeartbeats 3200000 in
lemma myBsImpl_complete (target : ℤ) (arr : Array ℤ) (lo hi p : Nat)
    (hhi : hi ≤ arr.size) (hnodup : subarray_nodup arr lo hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hp : lo ≤ p ∧ p < hi) (htarget : arr[p]! = target) :
    myBsImpl target arr lo hi = Int.ofNat p := by
  rw [myBsImpl_eq_myBs2]
  exact myBs2_complete target arr lo hi p hhi hnodup hrot hp htarget

-- Combined: if implementation returns Int.ofNat k, then k < length and nums[k]? = some target
lemma impl_finds_target' (nums : List ℤ) (target : ℤ) (k : Nat) :
    implementation nums target = Int.ofNat k →
    k < nums.length ∧ nums[k]? = some target := by
  rw [impl_unfold'] at *; intro h
  have hfind := myBsImpl_finds_target target nums.toArray 0 nums.toArray.size k
    (by rw [← h, bs_eq_myBsImpl])
  have hrange := myBsImpl_range target nums.toArray 0 nums.toArray.size k
    (by rw [← bs_eq_myBsImpl, h])
  aesop

-- Nodup list → subarray_nodup on its array
lemma list_nodup_impl (nums : List ℤ) (h_nodup : nums.Nodup) :
    subarray_nodup nums.toArray 0 nums.toArray.size := by
  intro i j _ hi _ hj heq; simp at hi hj
  have h1 : nums.toArray[i]! = nums[i] := by simp [getElem!_def, List.getElem?_eq_getElem hi]
  have h2 : nums.toArray[j]! = nums[j] := by simp [getElem!_def, List.getElem?_eq_getElem hj]
  exact h_nodup.getElem_inj_iff.mp (by rw [← h1, ← h2]; exact heq)

/-
PROBLEM
Helper: array element of rotated list equals corresponding base element

PROVIDED SOLUTION
Since hi : i < nums.toArray.size, we have i < nums.length (by simp). Use getElem!_def and List.getElem?_eq_getElem to convert nums.toArray[i]! to nums[i]. Then subst hk and use List.getElem_rotate to get (base.rotate k)[i] = base[(i + k) % base.length].
-/
lemma rotate_toArray_getElem (base nums : List ℤ) (k : ℕ) (hk : base.rotate k = nums)
    (hpos : base.length > 0) (i : ℕ) (hi : i < nums.toArray.size) :
    nums.toArray[i]! = base[(i + k) % base.length]'(Nat.mod_lt _ hpos) := by
  subst hk; simp_all +decide [ add_comm, List.getElem_rotate ] ;

/-
PROBLEM
Helper: strictly sorted base → any subrange of indices gives sorted elements

PROVIDED SOLUTION
Use List.pairwise_iff_getElem.mp hsorted to get the result directly. The statement gives i < j and j < base.length, so i < base.length by omega.
-/
lemma strict_sorted_subrange (base : List ℤ) (hsorted : base.Pairwise (· < ·))
    (i j : ℕ) (hij : i < j) (hj : j < base.length) :
    base[i]'(by omega) < base[j]'(by omega) := by
  rw [ List.pairwise_iff_get ] at hsorted;
  exact hsorted ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij

/-
PROBLEM
Helper: if m > 0 and a < b and a + m < n and b + m < n, then (a+m) % n < (b+m) % n

PROVIDED SOLUTION
Since a < b and b + m < n, we have a + m < n. So (a+m) % n = a+m and (b+m) % n = b+m (both < n). Then a+m < b+m follows from a < b. Use Nat.mod_eq_of_lt.
-/
lemma mod_lt_of_add_lt (a b m n : ℕ) (hab : a < b) (hbn : b + m < n) :
    (a + m) % n < (b + m) % n := by
  rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith

/-
PROBLEM
Helper: if m > 0, n - m ≤ a < b < n, then (a+m) % n < (b+m) % n

PROVIDED SOLUTION
Since n - m ≤ a and b < n, we have a + m ≥ n. So (a+m) % n = a + m - n. Similarly b + m ≥ n (since b ≥ a ≥ n-m), so (b+m) % n = b + m - n. Then (a+m-n) < (b+m-n) follows from a < b. Use Nat.add_mod_right or Nat.mod_eq_sub_mod to simplify.
-/
lemma mod_lt_of_add_wrap (a b m n : ℕ) (hab : a < b) (hbn : b < n)
    (han : n - m ≤ a) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    (a + m) % n < (b + m) % n := by
  have h_mod_eq : (a + m) % n = a + m - n ∧ (b + m) % n = b + m - n := by
    constructor <;> rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ hn, hm, hmn ];
    · rw [ Nat.mod_eq_of_lt ( by omega ) ];
    · omega;
    · rw [ Nat.mod_eq_of_lt ( by omega ) ];
    · omega;
  omega

/-
PROBLEM
isRotationOfStrictSorted → subarray_rot_sorted on array
This connects the high-level rotation property to the array-level property

PROVIDED SOLUTION
We have base strictly sorted (Pairwise <), base.rotate k = nums via hk.

Let m = k % base.length. Note base.length = nums.length (List.length_rotate). Also base.length > 0 since nums.Nodup and nums is a rotation of base.

Case m = 0: Then base.rotate k = base (since rotate by multiple of length is identity). So nums = base. Show subarray_sorted arr 0 arr.size. For any i < j < arr.size, use rotate_toArray_getElem to write arr[i]! = base[(i+k) % n] and arr[j]! = base[(j+k) % n]. Since m=0, (i+k) % n = i % n = i (since i < n), similarly for j. Then base[i] < base[j] by strict_sorted_subrange.

Case m > 0: The pivot q = nums.length - m satisfies 0 < q < nums.length.
- Left part [0, q): For i < j < q, (i+k) % n and (j+k) % n. Since i < q = n - m, i + m < n, so (i+k) % n = (i + k % n) % n. Actually use mod_lt_of_add_lt: since j < q = n - m, j + m < n, so (j+k) % n = j + m (mod n, but < n since j+m < n). Similarly for i. Then use strict_sorted_subrange.
Wait, let me be more careful. (i + k) % n. Since base.rotate k = nums and rotate only depends on k % n, we can WLOG assume k = m = k % n. So (i + k) % n where i < n - k and k < n gives i + k < n, so (i+k) % n = i + k. For j similarly. So base[i+k] < base[j+k] since i+k < j+k and j+k < n. Use strict_sorted_subrange.

- Right part [q, n): For q ≤ i < j < n where q = n - m. Then i + k ≥ n - m + m = n. So (i+k) % n = i+k-n. Similarly (j+k) % n = j+k-n. Since i < j, i+k-n < j+k-n. And j+k-n < n (since j < n and k = m < n). Use strict_sorted_subrange on base[i+k-n] < base[j+k-n], or use mod_lt_of_add_wrap then strict_sorted_subrange.

- Last < first: arr[n-1]! = base[(n-1+k) % n]. Since n-1 ≥ n-m = q, (n-1+k) % n = n-1+m-n = m-1. arr[0]! = base[(0+k) % n] = base[m]. So need base[m-1] < base[m], which follows from strict_sorted_subrange since m-1 < m < n (since m > 0 and m < n).

Use `rotate_toArray_getElem`, `strict_sorted_subrange`, `mod_lt_of_add_lt`, `mod_lt_of_add_wrap`.

Note: It helps to first establish hlen : base.length = nums.length (from List.length_rotate and hk), hpos : base.length > 0 (from nums.Nodup / h_nodup and length), and then use `set m := k % base.length` and note that base.rotate k = base.rotate m (List.rotate_mod).
-/
lemma list_rot_to_sa (nums : List ℤ)
    (h_rot : isRotationOfStrictSorted nums) (h_nodup : nums.Nodup) :
    subarray_rot_sorted nums.toArray 0 nums.toArray.size := by
  obtain ⟨base, h_sorted, _, h_is_rot⟩ := h_rot
  obtain ⟨k, hk⟩ := h_is_rot
  refine Classical.or_iff_not_imp_left.2 fun h => ?_;
  -- Let q be the position where the rotation starts, i.e., q = nums.length - (k % nums.length).
  obtain ⟨m, hm⟩ : ∃ m, k % nums.length = m ∧ 0 < m ∧ m < nums.length := by
    by_cases h_zero : k % nums.length = 0;
    · -- Since $k \mod nums.length = 0$, we have $base.rotate k = base$.
      have h_base : base.rotate k = base := by
        rw [ ← Nat.mod_add_div k nums.length, h_zero ] ; simp +decide [ List.rotate ] ;
        rw [ ← hk, List.length_rotate ] ; aesop;
      -- Since `base` is strictly sorted, `nums` must also be strictly sorted, contradicting `h`.
      have h_contra : subarray_sorted nums.toArray 0 nums.toArray.size := by
        intro i j hi hj hj'; have := h_sorted; simp_all +decide [ List.pairwise_iff_get ] ;
        rw [ List.getElem?_eq_getElem ];
        have := List.pairwise_iff_get.mp this;
        exact this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hj;
      contradiction;
    · exact ⟨ k % nums.length, rfl, Nat.pos_of_ne_zero h_zero, Nat.mod_lt _ ( List.length_pos_iff.mpr ( by aesop_cat ) ) ⟩;
  refine' ⟨ nums.length - m, _, _, _, _, _ ⟩ <;> simp_all +decide [ List.length_rotate ];
  · linarith;
  · -- For any i < j < nums.length - m, we have (i + k) % nums.length < (j + k) % nums.length.
    have h_mod_lt : ∀ i j, i < j → j < nums.length - m → (i + k) % nums.length < (j + k) % nums.length := by
      intros i j hij hjm
      have h_mod_lt : (i + k) % nums.length = (i + m) % nums.length ∧ (j + k) % nums.length = (j + m) % nums.length := by
        simp +decide [ ← hm.1, Nat.add_mod ];
      rw [ h_mod_lt.1, h_mod_lt.2, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega;
    intro i j hi hj hj'; have := h_mod_lt i j hj hj'; simp_all +decide [ List.getElem?_eq_getElem ] ;
    have h_mod_lt : nums[i]! = base[(i + k) % nums.length]! ∧ nums[j]! = base[(j + k) % nums.length]! := by
      have h_mod_lt : ∀ i, i < nums.length → nums[i]! = base[(i + k) % nums.length]! := by
        intro i hi; rw [ ← hk ] ; simp +decide [ List.getElem?_eq_getElem, hi ] ;
        rw [ List.getElem?_rotate ] ; aesop;
      exact ⟨ h_mod_lt i ( by omega ), h_mod_lt j ( by omega ) ⟩;
    have h_mod_lt : base[(i + k) % nums.length]! < base[(j + k) % nums.length]! := by
      have h_mod_lt : ∀ i j, i < j → j < base.length → base[i]! < base[j]! := by
        intros i j hij hj; exact (by
        have := List.pairwise_iff_get.mp h_sorted;
        convert this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij;
        · grind;
        · grind);
      apply h_mod_lt; exact ‹∀ i j : ℕ, i < j → j < nums.length - m → (i + k) % nums.length < (j + k) % nums.length› i j hj hj'; exact (by
      exact lt_of_lt_of_le ( Nat.mod_lt _ ( by linarith ) ) ( by simp [ ← hk, List.length_rotate ] ));
    grind +ring;
  · intro i j hi hj hj'; have := Nat.mod_add_div k nums.length; simp_all +decide [ List.getElem_rotate ] ;
    -- Since $i$ and $j$ are in the second part of the array, we have $i + m \geq \text{nums.length}$ and $j + m \geq \text{nums.length}$.
    have h_second_part : (i + m) % nums.length = i + m - nums.length ∧ (j + m) % nums.length = j + m - nums.length := by
      constructor <;> rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ Nat.mod_eq_of_lt, * ];
      · rw [ Nat.mod_eq_of_lt ( by omega ) ];
      · rw [ Nat.mod_eq_of_lt ( by omega ) ];
      · grind;
    have h_second_part : base[(i + m - nums.length)]! < base[(j + m - nums.length)]! := by
      have h_second_part : i + m - nums.length < j + m - nums.length ∧ j + m - nums.length < base.length := by
        have := congr_arg List.length hk; norm_num at this; omega;
      have := h_sorted; simp_all +decide [ isStrictSorted ] ;
      rw [ List.getElem?_eq_getElem ];
      exact List.pairwise_iff_get.mp h_sorted _ _ ( by simpa using h_second_part.1 );
      grind;
    have h_second_part : ∀ x : ℕ, x < nums.length → nums[x]! = base[(x + m) % nums.length]! := by
      intros x hx; rw [ ← hk ] ; simp +decide [ List.getElem_rotate, Nat.mod_eq_of_lt hx ] ;
      rw [ List.getElem?_rotate ] ; aesop;
      replace hk := congr_arg List.length hk ; aesop;
    grind;
  · have h_last_first : base[(nums.length - 1 + k) % nums.length]! < base[(0 + k) % nums.length]! := by
      have h_last_first : base[(nums.length - 1 + k) % nums.length]! = base[(m - 1)]! ∧ base[(0 + k) % nums.length]! = base[m]! := by
        simp +decide [ ← hm.1, Nat.add_mod, Nat.mod_eq_of_lt hm.2.2 ];
        rcases nums <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        rcases m with ( _ | m ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        norm_num [ ( by ring : List.length ‹_› + ( m + 1 ) = List.length ‹_› + 1 + m ) ];
        rw [ Nat.mod_eq_of_lt ( by linarith ) ];
      have h_last_first : ∀ i j, i < j → j < base.length → base[i]! < base[j]! := by
        intros i j hij hj; exact (by
        have := List.pairwise_iff_get.mp h_sorted;
        simpa [ List.getElem?_eq_getElem ( show i < base.length from by linarith ), List.getElem?_eq_getElem ( show j < base.length from by linarith ) ] using this ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ hij);
      convert h_last_first ( m - 1 ) m ( Nat.sub_lt hm.2.1 zero_lt_one ) _ using 1 <;> aesop;
    convert h_last_first using 1;
    · rw [ ← hk ];
      rw [ List.getElem?_rotate ];
      · aesop;
      · simp +arith +decide [ List.length_rotate ];
        contrapose! h; aesop;
    · rw [ ← hk, List.getElem?_eq_getElem ] <;> norm_num [ List.getElem_rotate ];
      rw [ List.getElem_rotate ];
      grind;
      contrapose! h; aesop

-- target ∈ nums → exists index in array
lemma mem_to_idx (nums : List ℤ) (target : ℤ) (hmem : target ∈ nums) :
    ∃ p, p < nums.toArray.size ∧ nums.toArray[p]! = target := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  exact ⟨i, by simp; exact hi, by simp [getElem!_def, List.getElem?_eq_getElem hi, hget]⟩

-- Uniqueness of index in nodup list
lemma nodup_uniq (nums : List ℤ) (target : ℤ) (h_nodup : nums.Nodup)
    (i j : Nat) (hi : i < nums.length) (hj : j < nums.length)
    (hti : nums[i]? = some target) (htj : nums[j]? = some target) : i = j := by
  have hti' : nums[i] = target := by
    rw [List.getElem?_eq_getElem hi] at hti; exact Option.some_injective _ hti
  have htj' : nums[j] = target := by
    rw [List.getElem?_eq_getElem hj] at htj; exact Option.some_injective _ htj
  exact (h_nodup.getElem_inj_iff).mp (by rw [hti', htj'])

end HelperLemmas

section Proof
set_option maxHeartbeats 800000

theorem correctness_goal_0_1 (nums : List ℤ) (target : ℤ) (h_len_pos : nums.length > 0) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hmem : inList nums target) (h_exists_idx : ∃ i < nums.length, nums[i]? = some target) : ∀ i < nums.length, nums[i]? = some target → implementation nums target = Int.ofNat i := by
    -- Get index p where target is in the array
    have ⟨p, hp_lt, hp_eq⟩ := mem_to_idx nums target hmem
    -- Use completeness to show implementation finds p
    have hsa_nodup := list_nodup_impl nums h_nodup
    have hsa_rot := list_rot_to_sa nums h_rot h_nodup
    have h_mybs := myBsImpl_complete target nums.toArray 0 nums.toArray.size p (le_refl _)
      hsa_nodup hsa_rot ⟨Nat.zero_le p, hp_lt⟩ hp_eq
    -- Convert to implementation result
    have h_bs : implementation.bs target nums.toArray 0 nums.toArray.size = Int.ofNat p := by
      rw [bs_eq_myBsImpl]; exact h_mybs
    have h_impl : implementation nums target = Int.ofNat p := by
      rw [impl_unfold']; exact h_bs
    -- For any i with nums[i]? = some target, i = p by uniqueness
    intro i hi hti
    have ⟨_, hget⟩ := impl_finds_target' nums target p h_impl
    have : p = i := nodup_uniq nums target h_nodup p i (by simp at hp_lt; exact hp_lt) hi hget hti
    rw [this] at h_impl; exact h_impl

theorem correctness_goal_2_1 (nums : List ℤ) (target : ℤ) (h_len_pos : nums.length > 0) (h_nodup : nums.Nodup) (h_rot : isRotationOfStrictSorted nums) (hmem : ¬inList nums target) (hne : ¬implementation nums target = -1) (i : ℕ) (hi : implementation nums target = Int.ofNat i) : inList nums target := by
    have ⟨hlt, hget⟩ := impl_finds_target' nums target i hi
    rw [List.getElem?_eq_some_iff] at hget
    obtain ⟨_, heq⟩ := hget
    rw [← heq]; exact List.getElem_mem ..
end Proof