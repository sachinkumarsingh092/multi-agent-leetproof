import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    1539. Kth Missing Positive Number: Given a strictly increasing array of positive integers `arr` and a positive integer `k`, return the k-th positive integer that does not appear in `arr`.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. The input `arr` is an array of natural numbers, intended to represent positive integers.
    2. The array is strictly increasing: each element is less than the next element.
    3. A positive integer `m` is considered "missing" if `m ≥ 1` and `m` is not an element of `arr`.
    4. For any `n ≥ 1`, we can count how many missing positive integers are in the range `[1, n]`.
    5. The desired output `result` is the unique positive integer such that:
       a. `result` is missing from `arr`.
       b. Exactly `k-1` missing positive integers are ≤ `result - 1`.
       c. Exactly `k` missing positive integers are ≤ `result`.
    6. These properties characterize the k-th missing positive integer without prescribing an algorithm.
-/

-- Boolean membership check for arrays of naturals.
-- We use Bool equality (==) to keep this decidable/computable.
def inArrayB (arr : Array Nat) (x : Nat) : Bool :=
  arr.any (fun y => y == x)

-- `arr` is strictly increasing.
def strictlyIncreasing (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! < arr[i + 1]!

-- Every element of `arr` is positive.
def allPositive (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i < arr.size → 0 < arr[i]!

-- Number of missing positive integers in the interval [1, n].
-- This is a computable definition using `Finset.Icc` and filtering by membership in `arr`.
def missingUpTo (arr : Array Nat) (n : Nat) : Nat :=
  ((Finset.Icc (1 : Nat) n).filter (fun m => !(inArrayB arr m))).card

-- Preconditions
-- `k` is positive and `arr` satisfies the problem's input constraints.
def precondition (arr : Array Nat) (k : Nat) : Prop :=
  k > 0 ∧ strictlyIncreasing arr ∧ allPositive arr

-- Postconditions
-- `result` is the k-th missing positive integer:
-- it is missing itself, and the missing-count just below it is k-1 while up to it is k.
def postcondition (arr : Array Nat) (k : Nat) (result : Nat) : Prop :=
  0 < result ∧
  inArrayB arr result = false ∧
  missingUpTo arr (Nat.pred result) = k - 1 ∧
  missingUpTo arr result = k
end Specs

section Impl
def implementation (arr : Array Nat) (k : Nat) : Nat :=
  -- missing count before index i (0-based) is arr[i] - (i+1)
  let n := arr.size
  if h0 : n = 0 then
    k
  else
    let missingAt (i : Nat) : Nat :=
      -- for i < n, arr[i]! is safe; otherwise this value is irrelevant
      arr[i]! - (i + 1)

    -- find the first index where missingAt i ≥ k, in range [lo, hi]
    let rec bs (lo hi : Nat) : Nat :=
      if h : lo < hi then
        let mid := lo + (hi - lo) / 2
        if missingAt mid < k then
          bs (mid + 1) hi
        else
          bs lo mid
      else
        lo
    termination_by hi - lo

    let idx := bs 0 n
    if hidx : idx = 0 then
      -- before the first element, the k-th missing is just k
      k
    else
      -- answer lies after arr[idx-1]
      let prevIdx := idx - 1
      let prevVal := arr[prevIdx]!
      let missPrev := missingAt prevIdx
      prevVal + (k - missPrev)
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [2,3,4,7,11], k = 5 => 9
def test1_arr : Array Nat := #[2, 3, 4, 7, 11]
def test1_k : Nat := 5
def test1_Expected : Nat := 9

-- Test case 2: Example 2
-- arr = [1,2,3,4], k = 2 => 6
def test2_arr : Array Nat := #[1, 2, 3, 4]
def test2_k : Nat := 2
def test2_Expected : Nat := 6

-- Test case 3: Empty array (vacuously strictly increasing); missing positives are [1,2,3,...]
def test3_arr : Array Nat := #[]
def test3_k : Nat := 1
def test3_Expected : Nat := 1

-- Test case 4: Single element not starting at 1
-- arr = [2]; missing positives are [1,3,4,...]
def test4_arr : Array Nat := #[2]
def test4_k : Nat := 1
def test4_Expected : Nat := 1

-- Test case 5: Single element starting at 1
-- arr = [1]; missing positives are [2,3,4,...]
def test5_arr : Array Nat := #[1]
def test5_k : Nat := 1
def test5_Expected : Nat := 2

-- Test case 6: Small gap inside array
-- arr = [1,3]; missing positives are [2,4,5,...]
def test6_arr : Array Nat := #[1, 3]
def test6_k : Nat := 1
def test6_Expected : Nat := 2

-- Test case 7: First few positives missing before the first element
-- arr = [5,6,7]; missing positives are [1,2,3,4,8,9,...]
def test7_arr : Array Nat := #[5, 6, 7]
def test7_k : Nat := 2
def test7_Expected : Nat := 2

-- Test case 8: Large jump later in the array
-- arr = [1,2,100]; missing positives are [3..99] then [101..]
-- 97th missing is 99
def test8_arr : Array Nat := #[1, 2, 100]
def test8_k : Nat := 97
def test8_Expected : Nat := 99

-- Test case 9: Same array as example 1 but smallest valid k
-- missing positives start with 1
def test9_arr : Array Nat := #[2, 3, 4, 7, 11]
def test9_k : Nat := 1
def test9_Expected : Nat := 1
end TestCases

section Helpers

/-! ### Basic properties of strictly increasing arrays -/

/-
PROVIDED SOLUTION
By induction on j - i. Base case: j = i + 1, use strictlyIncreasing directly. Inductive step: arr[i]! < arr[j-1]! < arr[j]! by induction hypothesis and strictlyIncreasing.
-/
lemma arr_strict_mono (arr : Array Nat) (h : strictlyIncreasing arr)
    (i j : Nat) (hij : i < j) (hj : j < arr.size) : arr[i]! < arr[j]! := by
  -- Since `arr` is strictly increasing, we have `arr[i]! < arr[i + 1]!` for all `i`.
  have h_strict : ∀ i, i + 1 < arr.size → arr[i]! < arr[i + 1]! := by
    exact?;
  -- By induction on $j - i$, we can show that $arr[i]! < arr[j]!$ for any $i < j$.
  induction' hij with j hj ih;
  · exact h_strict i hj;
  · exact lt_trans ( ih ( Nat.lt_of_succ_lt hj ) ) ( h_strict _ hj )

/-
PROVIDED SOLUTION
By induction on i. Base: arr[0]! ≥ 1 from allPositive. Step: arr[i+1]! > arr[i]! ≥ i+1 from strictlyIncreasing and IH, so arr[i+1]! ≥ i+2.
-/
lemma arr_ge_succ (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (i : Nat) (hi : i < arr.size) : arr[i]! ≥ i + 1 := by
  induction' i with i ih;
  · exact h_pos 0 hi;
  · exact Nat.succ_le_of_lt ( lt_of_le_of_lt ( ih ( Nat.lt_of_succ_lt hi ) ) ( h_inc i ( by linarith ) ) )

/-! ### inArrayB characterization -/

/-
PROVIDED SOLUTION
Unfold inArrayB as arr.any. Use Array.any_iff_exists or similar. The negation of "exists y in arr such that y == x" is "for all indices i, arr[i]! ≠ x".
-/
lemma not_inArrayB_iff (arr : Array Nat) (x : Nat) :
    inArrayB arr x = false ↔ ∀ i, i < arr.size → arr[i]! ≠ x := by
  unfold inArrayB; aesop;

/-! ### Count of arr elements in [1, n] for strictly increasing positive arrays -/

/-
PROVIDED SOLUTION
We show a bijection between {m ∈ [1,n] : inArrayB arr m} and {i ∈ range(arr.size) : arr[i]! ≤ n}.

The map i ↦ arr[i]! is an injection from the RHS to the LHS (injective because arr is strictly increasing, and arr[i]! ∈ [1,n] because arr[i]! ≥ 1 by allPositive and arr[i]! ≤ n by the filter condition, and inArrayB arr (arr[i]!) is true).

The inverse: for m ∈ LHS, inArrayB arr m means there exists i < arr.size with arr[i]! = m; this i is unique by strict monotonicity; and arr[i]! = m ≤ n means i is in the RHS.

Use Finset.card_bij or Finset.card_image_of_injOn to establish the equality.
-/
lemma count_arr_in_icc (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (n : Nat) :
    ((Finset.Icc 1 n).filter (fun m => inArrayB arr m)).card =
    ((Finset.range arr.size).filter (fun i => arr[i]! ≤ n)).card := by
  have h_bij : Finset.filter (fun m => inArrayB arr m = true) (Finset.Icc 1 n) = Finset.image (fun i => arr[i]!) (Finset.filter (fun i => arr[i]! ≤ n) (Finset.range arr.size)) := by
    ext m
    simp [inArrayB, Finset.mem_image];
    constructor <;> intro h;
    · obtain ⟨ i, hi, rfl ⟩ := h.2; use i; aesop;
    · obtain ⟨ i, ⟨ hi₁, hi₂ ⟩, rfl ⟩ := h; use ⟨ ?_, hi₂ ⟩ ; use i; aesop;
      exact h_pos i hi₁;
  rw [ h_bij, Finset.card_image_of_injOn ];
  intros i hi j hj hij;
  have h_strict_mono : ∀ i j, i < j → i < arr.size → j < arr.size → arr[i]! < arr[j]! := by
    exact?;
  exact le_antisymm ( le_of_not_gt fun hi' => by linarith [ h_strict_mono _ _ hi' ( by aesop ) ( by aesop ) ] ) ( le_of_not_gt fun hj' => by linarith [ h_strict_mono _ _ hj' ( by aesop ) ( by aesop ) ] )

/-
PROVIDED SOLUTION
The filter {i ∈ range(arr.size) : arr[i]! ≤ n} equals range(idx). For i < idx, arr[i]! ≤ n by h_below. For i ≥ idx and i < arr.size, n < arr[i]! by h_above, so arr[i]! > n, i.e., ¬(arr[i]! ≤ n). So the filter is exactly {0, ..., idx-1} = range(idx). The cardinality of range(idx) is idx.
-/
lemma count_le_indices (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (n idx : Nat) (hidx : idx ≤ arr.size)
    (h_below : ∀ i, i < idx → arr[i]! ≤ n)
    (h_above : ∀ i, idx ≤ i → i < arr.size → n < arr[i]!) :
    ((Finset.range arr.size).filter (fun i => arr[i]! ≤ n)).card = idx := by
  convert Finset.card_range idx;
  grind +ring

/-! ### Key formula: missingUpTo when we know the cutoff index -/

/-
PROVIDED SOLUTION
missingUpTo arr n = |{m ∈ [1,n] : ¬inArrayB arr m}| = |[1,n]| - |{m ∈ [1,n] : inArrayB arr m}| = n - count_arr_in_icc = n - count_le_indices = n - idx. Use Finset.card_sdiff or Finset.filter_not_card to get the complement, then apply count_arr_in_icc and count_le_indices.
-/
lemma missingUpTo_with_cutoff (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (h_pos : allPositive arr) (n idx : Nat) (hidx : idx ≤ arr.size)
    (h_below : ∀ i, i < idx → arr[i]! ≤ n)
    (h_above : ∀ i, idx ≤ i → i < arr.size → n < arr[i]!) :
    missingUpTo arr n = n - idx := by
  unfold missingUpTo;
  convert congr_arg ( fun x : ℕ => n - x ) ( count_arr_in_icc arr h_inc h_pos n ) using 1;
  · simp +zetaDelta at *;
    rw [ show { m ∈ Finset.Icc 1 n | inArrayB arr m = false } = Finset.Icc 1 n \ { m ∈ Finset.Icc 1 n | inArrayB arr m = true } by ext; aesop, Finset.card_sdiff ] ; norm_num;
    rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ];
  · rw [ count_le_indices arr h_inc n idx hidx h_below h_above ]

/-! ### Monotonicity of missingAt -/

/-
PROVIDED SOLUTION
We need arr[i]! - (i+1) ≤ arr[j]! - (j+1). Since arr is strictly increasing with i ≤ j, if i = j it's trivial. If i < j, then arr[j]! ≥ arr[i]! + (j - i) (because each step increases by at least 1). So arr[j]! - (j+1) ≥ arr[i]! + (j-i) - (j+1) = arr[i]! - (i+1). The key facts are arr_ge_succ (so arr[i]! ≥ i+1, meaning the subtractions don't underflow) and arr_strict_mono (arr[i]! < arr[j]! when i < j, and more specifically arr[j]! ≥ arr[i]! + (j - i) by iterating the strict increase).
-/
lemma missingAt_mono (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (i j : Nat) (hij : i ≤ j) (hj : j < arr.size) :
    arr[i]! - (i + 1) ≤ arr[j]! - (j + 1) := by
  -- Since arr is strictly increasing, we have arr[j]! ≥ arr[i]! + (j - i).
  have h_arr_step : arr[j]! ≥ arr[i]! + (j - i) := by
    -- By induction on $j - i$, we can show that $arr[j]! \geq arr[i]! + (j - i)$.
    induction' hij with j hj ih;
    · norm_num;
    · rw [ Nat.succ_sub ( by linarith [ Nat.succ_le_succ ‹i.le j› ] ) ];
      linarith [ ih ( Nat.lt_of_succ_lt hj ), h_inc j ( by linarith ) ];
  omega

/-! ### Binary search specification -/

/-
PROVIDED SOLUTION
By strong induction on hi - lo.

Base case (lo = hi): idx = lo. All four conjuncts hold: lo ≤ lo, lo ≤ hi, the universal quantifiers are vacuous (no j with lo ≤ j < lo), and idx < hi is false.

Inductive step (lo < hi): Let mid = lo + (hi - lo) / 2. Note lo ≤ mid < hi.

Case 1: missingAt mid < k. Recurse on bs (mid+1) hi. By IH (since hi - (mid+1) < hi - lo):
- mid+1 ≤ idx ≤ hi
- ∀ j, mid+1 ≤ j → j < idx → missingAt j < k
- idx < hi → k ≤ missingAt idx

We need: ∀ j, lo ≤ j → j < idx → missingAt j < k. For j ≥ mid+1, use IH. For j ≤ mid, since missingAt is monotone and missingAt mid < k, we have missingAt j ≤ missingAt mid < k.

The monotonicity hypothesis for the recursive call: ∀ i j, mid+1 ≤ i → i ≤ j → j < hi → missingAt i ≤ missingAt j. This follows from the original hmono since mid+1 ≥ lo.

Case 2: missingAt mid ≥ k. Recurse on bs lo mid. By IH (since mid - lo < hi - lo):
- lo ≤ idx ≤ mid
- ∀ j, lo ≤ j → j < idx → missingAt j < k
- idx < mid → k ≤ missingAt idx

We need: idx < hi → k ≤ missingAt idx. Since idx ≤ mid < hi, if idx < mid, IH gives k ≤ missingAt idx. If idx = mid, then missingAt mid ≥ k.

The monotonicity hypothesis for the recursive call: ∀ i j, lo ≤ i → i ≤ j → j < mid → missingAt i ≤ missingAt j. This follows from the original hmono since mid < hi.

Use `unfold implementation.bs` to expose the recursion, then split_ifs.
-/
lemma bs_spec (k : Nat) (missingAt : Nat → Nat)
    (lo hi : Nat) (hle : lo ≤ hi)
    (hmono : ∀ i j, lo ≤ i → i ≤ j → j < hi → missingAt i ≤ missingAt j) :
    let idx := implementation.bs k missingAt lo hi
    lo ≤ idx ∧ idx ≤ hi ∧
    (∀ j, lo ≤ j → j < idx → missingAt j < k) ∧
    (idx < hi → k ≤ missingAt idx) := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi k missingAt;
  -- Let's consider the two cases: lo < hi and lo = hi.
  by_cases h_cases : lo < hi;
  · unfold implementation.bs; simp +decide [ h_cases ] ;
    split_ifs;
    · specialize ih ( hi - ( lo + ( hi - lo ) / 2 + 1 ) ) ?_ k missingAt ( lo + ( hi - lo ) / 2 + 1 ) hi ?_ ?_ rfl <;> norm_num at *;
      · omega;
      · omega;
      · exact fun i j hi hj hj' => hmono i j ( by omega ) hj hj';
      · refine' ⟨ by omega, ih.2.1, fun j hj₁ hj₂ => _, ih.2.2.2 ⟩;
        by_cases hj₃ : j < lo + (hi - lo) / 2 + 1;
        · exact lt_of_le_of_lt ( hmono _ _ hj₁ ( by omega ) ( by omega ) ) ‹missingAt ( lo + ( hi - lo ) / 2 ) < k›;
        · exact ih.2.2.1 j ( by linarith ) hj₂;
    · specialize ih ( ( lo + ( hi - lo ) / 2 ) - lo ) ?_ k missingAt lo ( lo + ( hi - lo ) / 2 ) ?_ ?_ rfl <;> norm_num at *;
      · omega;
      · exact fun i j hi hj hj' => hmono i j hi hj ( by omega );
      · grind;
  · unfold implementation.bs;
    grind

/-! ### Cutoff properties given binary search result -/

/-
PROVIDED SOLUTION
If i < idx - 1, then arr[i]! < arr[idx-1]! ≤ n by arr_strict_mono. If i = idx - 1, then arr[i]! = arr[idx-1]! ≤ n directly from hn.
-/
lemma below_cutoff_le (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (idx : Nat) (hidx : 0 < idx) (hidx2 : idx ≤ arr.size)
    (n : Nat) (hn : arr[idx - 1]! ≤ n) (i : Nat) (hi : i < idx) :
    arr[i]! ≤ n := by
  -- By the properties of strictly increasing arrays, if $i < idx$, then $arr[i]! < arr[idx - 1]!$.
  have h_lt : i < idx - 1 → arr[i]! < arr[idx - 1]! := by
    exact fun hi' => arr_strict_mono arr h_inc i ( idx - 1 ) hi' ( by omega );
  grind

/-
PROVIDED SOLUTION
If i = idx, then n < arr[idx]! = arr[i]! directly. If i > idx, then arr[idx]! < arr[i]! by arr_strict_mono, so n < arr[idx]! < arr[i]!.
-/
lemma above_cutoff_gt (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (idx : Nat) (hidx2 : idx < arr.size)
    (n : Nat) (hn : n < arr[idx]!) (i : Nat) (hi : idx ≤ i)
    (hi2 : i < arr.size) :
    n < arr[i]! := by
  -- By induction on $i - \text{idx}$, we can show that $arr[i]! > n$ for all $i \geq \text{idx}$.
  induction' hi with i hi ih;
  · assumption;
  · exact lt_trans ( ih ( Nat.lt_of_succ_lt hi2 ) ) ( h_inc _ hi2 )

/-
PROVIDED SOLUTION
Use not_inArrayB_iff. For any index i < arr.size, we need arr[i]! ≠ result. If i < idx, then arr[i]! ≤ arr[idx-1]! < result (using arr_strict_mono). If i ≥ idx and idx < arr.size, then result < arr[idx]! ≤ arr[i]! (using arr_strict_mono or equal). If idx = arr.size, then i < idx is i < arr.size so all indices are covered by the first case.
-/
lemma result_not_in_arr (arr : Array Nat) (h_inc : strictlyIncreasing arr)
    (idx : Nat) (hidx : 0 < idx) (hidx2 : idx ≤ arr.size)
    (result : Nat)
    (hgt : arr[idx - 1]! < result)
    (hlt : idx = arr.size ∨ result < arr[idx]!) :
    inArrayB arr result = false := by
  by_contra h_contra;
  obtain ⟨i, hi⟩ : ∃ i, i < arr.size ∧ arr[i]! = result := by
    unfold inArrayB at h_contra; aesop;
  -- If $i < idx$, then $arr[i]! \leq arr[idx-1]!$ by definition of `arr`.
  by_cases h_cases : i < idx;
  · have h_le : arr[i]! ≤ arr[idx - 1]! := by
      by_cases h_cases2 : i < idx - 1;
      · exact le_of_lt ( arr_strict_mono arr h_inc i ( idx - 1 ) h_cases2 ( by omega ) );
      · rw [ show i = idx - 1 by omega ];
    linarith;
  · cases hlt <;> simp_all +decide [ Nat.sub_add_cancel hidx ];
    linarith [ arr_strict_mono arr h_inc idx i ( lt_of_le_of_ne h_cases ( Ne.symm <| by aesop ) ) hi.1 ]

/-! ### Arithmetic lemmas for the result -/

/-
PROVIDED SOLUTION
We have arr[idx-1]! ≥ (idx-1) + 1 = idx from arr_ge_succ. So arr[idx-1]! - ((idx-1)+1) = arr[idx-1]! - idx. Then arr[idx-1]! + (k - (arr[idx-1]! - idx)) = arr[idx-1]! + k - arr[idx-1]! + idx = idx + k. The key is that arr[idx-1]! ≥ idx so the subtraction doesn't underflow.
-/
lemma result_eq_idx_plus_k (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (idx k : Nat) (hidx : 0 < idx) (hidx2 : idx ≤ arr.size)
    (hmiss_lt : arr[idx-1]! - ((idx-1) + 1) < k) :
    arr[idx-1]! + (k - (arr[idx-1]! - ((idx-1) + 1))) = idx + k := by
  -- By definition of `arr_ge_succ`, we know that `arr[idx - 1]! ≥ idx`.
  have h_arr_ge_idx : arr[idx - 1]! ≥ idx := by
    convert arr_ge_succ arr h_inc h_pos ( idx - 1 ) ( Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hidx ) ) hidx2 ) using 1;
    rw [ Nat.sub_add_cancel hidx ];
  omega

/-
PROVIDED SOLUTION
From arr_ge_succ, arr[idx-1]! ≥ idx. The hypothesis says arr[idx-1]! - idx < k. So arr[idx-1]! < idx + k (since if arr[idx-1]! ≥ idx + k, then arr[idx-1]! - idx ≥ k, contradiction).
-/
lemma result_gt_prev (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (idx k : Nat) (hidx : 0 < idx) (hidx2 : idx ≤ arr.size)
    (hk : k > 0)
    (hmiss_lt : arr[idx-1]! - ((idx-1) + 1) < k) :
    arr[idx-1]! < idx + k := by
  omega

/-
PROVIDED SOLUTION
hmiss_ge says k ≤ arr[idx]! - (idx + 1). So idx + 1 + k ≤ arr[idx]!, hence idx + k < arr[idx]!.
-/
lemma result_lt_next (arr : Array Nat) (h_inc : strictlyIncreasing arr) (h_pos : allPositive arr)
    (idx k : Nat) (hidx2 : idx < arr.size)
    (hmiss_ge : k ≤ arr[idx]! - (idx + 1)) :
    idx + k < arr[idx]! := by
  contrapose! hmiss_ge;
  rw [ tsub_lt_iff_left ] <;> linarith [ arr_ge_succ arr h_inc h_pos idx hidx2 ] ;

end Helpers

section Proof

theorem correctness_goal_1 (arr : Array ℕ) (k : ℕ) (h_precond : precondition arr k)
    (h0 : ¬arr.size = 0) : postcondition arr k (implementation arr k) := by
  obtain ⟨hk, h_inc, h_pos⟩ := h_precond
  have hsize : arr.size > 0 := Nat.pos_of_ne_zero h0
  unfold implementation
  simp only [h0, ↓reduceDIte]
  -- Set idx for readability
  set idx := implementation.bs k (fun i => arr[i]! - (i + 1)) 0 arr.size with idx_def
  -- Binary search spec
  have hmono : ∀ i j, 0 ≤ i → i ≤ j → j < arr.size → arr[i]! - (i + 1) ≤ arr[j]! - (j + 1) := by
    intro i j _ hij hj; exact missingAt_mono arr h_inc h_pos i j hij hj
  have hbs := bs_spec k (fun i => arr[i]! - (i + 1)) 0 arr.size (Nat.zero_le _) hmono
  change 0 ≤ idx ∧ idx ≤ arr.size ∧
    (∀ j, 0 ≤ j → j < idx → arr[j]! - (j + 1) < k) ∧
    (idx < arr.size → k ≤ arr[idx]! - (idx + 1)) at hbs
  obtain ⟨_, hhi, hall_lt, hge⟩ := hbs
  -- Split on whether idx = 0
  split
  · -- Case idx = 0
    rename_i hidx
    -- missingAt 0 >= k
    have hmiss0 : k ≤ arr[0]! - (0 + 1) := by
      have := hge (show idx < arr.size by omega)
      rwa [hidx] at this
    have harr0_ge : arr[0]! ≥ k + 1 := by omega
    -- All array elements > k
    have hall_gt_k : ∀ i, i < arr.size → arr[i]! > k := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · omega
      · have := arr_strict_mono arr h_inc 0 i hi0 hi; omega
    -- k not in array
    have hk_not_in : inArrayB arr k = false := by
      rw [not_inArrayB_iff]; intro i hi heq; have := hall_gt_k i hi; omega
    -- All [1..k] not in arr
    have hall_not_in : ∀ m, 1 ≤ m → m ≤ k → inArrayB arr m = false := by
      intro m _ hmk; rw [not_inArrayB_iff]; intro i hi heq; have := hall_gt_k i hi; omega
    -- missingUpTo arr k = k
    have hmissing_k : missingUpTo arr k = k := by
      unfold missingUpTo
      have hf : (Finset.Icc 1 k).filter (fun m => !(inArrayB arr m)) = Finset.Icc 1 k := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun ⟨h, _⟩ => h, fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, by simp [hall_not_in m h1 h2]⟩⟩
      rw [hf]; simp
    -- missingUpTo arr (k-1) = k-1
    have hmissing_pred : missingUpTo arr (k - 1) = k - 1 := by
      unfold missingUpTo
      have hf : (Finset.Icc 1 (k-1)).filter (fun m => !(inArrayB arr m)) = Finset.Icc 1 (k-1) := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun ⟨h, _⟩ => h, fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, by simp [hall_not_in m h1 (by omega)]⟩⟩
      rw [hf]; simp
    exact ⟨hk, hk_not_in, by simp [Nat.pred_eq_sub_one, hmissing_pred], hmissing_k⟩
  · -- Case idx ≠ 0
    rename_i hidx
    have hidx_pos : 0 < idx := Nat.pos_of_ne_zero hidx
    -- missingAt(idx-1) < k
    have hmiss_prev_lt : arr[idx-1]! - ((idx-1) + 1) < k := hall_lt (idx - 1) (by omega) (by omega)
    -- Either idx = arr.size or (idx < arr.size and missingAt(idx) >= k)
    have hmiss_or : idx = arr.size ∨ (idx < arr.size ∧ k ≤ arr[idx]! - (idx + 1)) := by
      by_cases h : idx < arr.size
      · exact Or.inr ⟨h, hge h⟩
      · exact Or.inl (by omega)
    -- result = idx + k
    have hresult_eq : arr[idx - 1]! + (k - (arr[idx - 1]! - (idx - 1 + 1))) = idx + k :=
      result_eq_idx_plus_k arr h_inc h_pos idx k hidx_pos (by omega) hmiss_prev_lt
    -- result > arr[idx-1]!
    have hresult_gt : arr[idx - 1]! < idx + k :=
      result_gt_prev arr h_inc h_pos idx k hidx_pos (by omega) hk hmiss_prev_lt
    -- result < arr[idx]! (when idx < arr.size)
    have hresult_lt : idx = arr.size ∨ idx + k < arr[idx]! := by
      rcases hmiss_or with heq | ⟨hidx_lt, hmiss_ge⟩
      · exact Or.inl heq
      · exact Or.inr (result_lt_next arr h_inc h_pos idx k hidx_lt hmiss_ge)
    -- result not in arr
    have hresult_not_in : inArrayB arr (idx + k) = false :=
      result_not_in_arr arr h_inc idx hidx_pos (by omega) (idx + k) hresult_gt hresult_lt
    -- missingUpTo arr (idx + k) = k
    have hmissing_result : missingUpTo arr (idx + k) = k := by
      have h1 := missingUpTo_with_cutoff arr h_inc h_pos (idx + k) idx (by omega)
        (fun i hi => below_cutoff_le arr h_inc idx hidx_pos (by omega) (idx + k) (by omega) i hi)
        (fun i hi hi2 => by
          rcases hresult_lt with heq | hlt
          · omega
          · exact above_cutoff_gt arr h_inc idx (by omega) (idx + k) hlt i hi hi2)
      omega
    -- missingUpTo arr (idx + k - 1) = k - 1
    have hmissing_pred : missingUpTo arr (idx + k - 1) = k - 1 := by
      have h1 := missingUpTo_with_cutoff arr h_inc h_pos (idx + k - 1) idx (by omega)
        (fun i hi => by
          have h2 := below_cutoff_le arr h_inc idx hidx_pos (by omega) (idx + k - 1) (by omega) i hi
          exact h2)
        (fun i hi hi2 => by
          rcases hresult_lt with heq | hlt
          · omega
          · have := above_cutoff_gt arr h_inc idx (by omega) (idx + k) hlt i hi hi2; omega)
      omega
    -- Assemble postcondition
    constructor
    · omega
    constructor
    · rw [hresult_eq]; exact hresult_not_in
    constructor
    · simp only [Nat.pred_eq_sub_one, hresult_eq]; exact hmissing_pred
    · rw [hresult_eq]; exact hmissing_result

end Proof