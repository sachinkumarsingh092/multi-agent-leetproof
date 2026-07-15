import Lean
import Mathlib.Tactic

set_option maxHeartbeats 800000

def myBs2 (target : ℤ) (arr : Array ℤ) (lo hi : Nat) : ℤ :=
  if h : lo < hi then
    let mid : Nat := lo + (hi - lo) / 2
    let midVal : ℤ := arr[mid]!
    if midVal = target then
      Int.ofNat mid
    else
      let loVal : ℤ := arr[lo]!
      if loVal ≤ midVal then
        if loVal ≤ target ∧ target < midVal then
          myBs2 target arr lo mid
        else
          myBs2 target arr (mid + 1) hi
      else
        let hiVal : ℤ := arr[hi - 1]!
        if midVal < target ∧ target ≤ hiVal then
          myBs2 target arr (mid + 1) hi
        else
          myBs2 target arr lo mid
  else
    (-1)
termination_by hi - lo

def subarray_sorted (arr : Array ℤ) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < j → j < hi → arr[i]! < arr[j]!

def subarray_nodup (arr : Array ℤ) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < hi → lo ≤ j → j < hi → arr[i]! = arr[j]! → i = j

def subarray_rot_sorted (arr : Array ℤ) (lo hi : Nat) : Prop :=
  subarray_sorted arr lo hi ∨
  (∃ q, lo < q ∧ q < hi ∧
    subarray_sorted arr lo q ∧
    subarray_sorted arr q hi ∧
    arr[hi-1]! < arr[lo]!)

/-
PROBLEM
Helper 1: if arr[lo] ≤ arr[mid] in a rot_sorted array, left half [lo, mid+1) is sorted

PROVIDED SOLUTION
Case 1 (sorted): sub-interval of sorted is sorted. Apply hrot with bounds ≤ mid+1.
Case 2 (pivot q): Show q > mid. If q ≤ mid, then since [q, hi) is sorted, arr[q] ≤ arr[mid]. Since [lo, q) sorted, arr[lo] ≤ arr[q-1] if q > lo+1. Also arr[q] ≤ arr[hi-1] < arr[lo] (by hq₅). So arr[mid] ≥ arr[q] (sorted in [q,hi)) but arr[q] ≤ arr[hi-1] < arr[lo], hence arr[mid] < arr[lo], contradicting hle. So q > mid, and [lo, mid+1) ⊆ [lo, q) which is sorted.
-/
lemma rot_sorted_left_sorted (arr : Array ℤ) (lo hi mid : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_lt : mid < hi)
    (hnodup : subarray_nodup arr lo hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hle : arr[lo]! ≤ arr[mid]!) :
    subarray_sorted arr lo (mid + 1) := by
  cases hrot;
  · intro i j hij hji;
    exact fun h => ‹subarray_sorted arr lo hi› i j hij hji ( by linarith );
  · rename_i h;
    obtain ⟨ q, hq₁, hq₂, hq₃, hq₄, hq₅ ⟩ := h;
    by_cases hq_mid : q ≤ mid;
    · contrapose! hq₅;
      refine' le_trans _ ( show arr[mid]! ≤ arr[hi - 1]! from _ );
      · linarith;
      · by_cases hmid_eq_hi_minus_1 : mid = hi - 1;
        · rw [ hmid_eq_hi_minus_1 ];
        · exact hq₄ _ _ ( by linarith ) ( by omega ) ( by omega ) |> le_of_lt;
    · exact fun i j hi hj hj' => hq₃ i j hi hj ( by linarith )

/-
PROBLEM
Helper 2: if arr[lo] > arr[mid] in a rot_sorted array, right half [mid, hi) is sorted

PROVIDED SOLUTION
Case 1 (sorted): If the whole array is sorted, arr[lo] < arr[mid] when lo < mid, contradicting hgt. If lo = mid, arr[lo] = arr[mid], contradicting hgt. So case 1 is impossible.
Case 2 (pivot q): Show q ≤ mid. If q > mid, since [lo, q) is sorted, if lo < mid then arr[lo] < arr[mid], contradicting hgt. If lo = mid, arr[lo] = arr[mid], contradicting hgt. So q ≤ mid. Then [mid, hi) ⊆ [q, hi) which is sorted by hq₄.
-/
lemma rot_sorted_right_sorted (arr : Array ℤ) (lo hi mid : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_lt : mid < hi)
    (hnodup : subarray_nodup arr lo hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hgt : arr[lo]! > arr[mid]!) :
    subarray_sorted arr mid hi := by
  -- Apply the definition of subarray_rot_sorted to get the two cases.
  obtain h | ⟨q, hq₁, hq₂, hq₃, hq₄, hq₅⟩ := hrot;
  · exact fun i j hi_lt hj_lt hij => h i j ( by linarith ) ( by linarith ) ( by linarith );
  · -- If q > mid, then since [lo, q) is sorted, if lo < mid then arr[lo] < arr[mid], contradicting hgt. If lo = mid, arr[lo] = arr[mid], contradicting hgt. So q ≤ mid.
    by_cases hq_mid : q > mid;
    · have h_contra : arr[lo]! < arr[mid]! := by
        cases eq_or_lt_of_le hmid_lo <;> aesop;
      linarith;
    · exact fun i j hi hj hij => hq₄ i j ( by linarith ) ( by linarith ) ( by linarith )

/-
PROBLEM
Helper 3: in a sorted sub-array, if lo ≤ p < hi, then arr[lo] ≤ arr[p] ≤ arr[hi-1]

PROVIDED SOLUTION
Split into two parts:
1. arr[lo]! ≤ arr[p]!: If lo = p, trivial. If lo < p, then by hsort (lo, p), arr[lo]! < arr[p]!, so ≤.
2. arr[p]! ≤ arr[hi-1]!: If p = hi-1, trivial. If p < hi-1, then by hsort (p, hi-1), arr[p]! < arr[hi-1]!, so ≤.

Use: constructor; rcases with rfl or lt; exact le_of_lt (hsort ...)
-/
lemma sorted_target_in_range (arr : Array ℤ) (lo hi p : Nat)
    (hlo : lo < hi) (hp : lo ≤ p ∧ p < hi)
    (hsort : subarray_sorted arr lo hi) :
    arr[lo]! ≤ arr[p]! ∧ arr[p]! ≤ arr[hi-1]! := by
  constructor;
  · exact le_of_not_gt fun h => by have := hsort lo p ( by linarith ) ( lt_of_le_of_ne hp.1 ( by aesop ) ) ( by linarith ) ; linarith;
  · by_cases h_cases : p = hi - 1;
    · rw [ h_cases ];
    · exact le_of_lt ( hsort _ _ ( by omega ) ( by omega ) ( by omega ) )

/-
PROBLEM
Helper 5: rot_sorted sub-intervals (right)

PROVIDED SOLUTION
Show [mid+1, hi) is rotated sorted given [lo, hi) is rotated sorted and [lo, mid+1) is sorted.

Case 1 ([lo, hi) is sorted): Then [mid+1, hi) is also sorted (sub-interval of sorted), hence rot_sorted (Left case).

Case 2 ([lo, hi) has pivot q):
- If q ≤ mid+1: Since [lo, mid+1) is sorted and q ≤ mid+1, and [q, hi) is sorted, then [mid+1, hi) ⊆ [q, hi) which is sorted.
- If q > mid+1: The pivot q is in [mid+1, hi). [lo, q) is sorted so [mid+1, q) ⊆ [lo, q) is sorted. [q, hi) is sorted. arr[hi-1] < arr[lo] ≤ arr[mid+1] (since [lo, mid+1) is sorted and mid+1 ≤ q means mid+1 < q, so arr[lo] ≤ arr[mid] < arr[mid+1]). Wait, arr[lo] ≤ arr[mid] by [lo, mid+1) sorted. And arr[mid+1] could be... hmm.

Actually: arr[hi-1] < arr[lo] (from hq₅). arr[lo] ≤ arr[mid] (by hleft_sorted if lo < mid). And arr[lo..q) is sorted, so arr[mid+1] > arr[lo] if mid+1 < q and mid+1 ≥ lo. So arr[hi-1] < arr[lo] ≤ arr[mid+1].

So for [mid+1, hi): pivot is at q, [mid+1, q) ⊆ [lo, q) is sorted, [q, hi) is sorted, arr[hi-1] < arr[mid+1]. This gives rot_sorted.
-/
lemma rot_sorted_right_sub (arr : Array ℤ) (lo hi mid : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_hi : mid < hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hleft_sorted : subarray_sorted arr lo (mid + 1)) :
    subarray_rot_sorted arr (mid + 1) hi := by
  cases hrot <;> simp_all +decide [ subarray_sorted ];
  · exact Or.inl fun i j hi hj hlt => by rename_i h; exact h i j ( by linarith ) ( by linarith ) ( by linarith ) ;
  · obtain ⟨q, hq⟩ := ‹∃ q, lo < q ∧ q < hi ∧ (∀ i j, lo ≤ i → i < j → j < q → arr[i]! < arr[j]!) ∧ (∀ i j, q ≤ i → i < j → j < hi → arr[i]! < arr[j]!) ∧ arr[hi - 1]! < arr[lo]!›
    by_cases hq_le : q ≤ mid + 1;
    · refine Or.inl ?_;
      intro i j hi hj hj'; exact hq.2.2.2.1 i j ( by linarith ) ( by linarith ) ( by linarith ) ;
    · refine' Or.inr ⟨ q, _, _, _, _, _ ⟩ <;> try linarith;
      · intro i j hi hj hq_lt; exact hq.2.2.1 i j ( by linarith ) ( by linarith ) ( by linarith ) ;
      · exact fun i j hi hj hj' => hq.2.2.2.1 i j hi hj hj';
      · linarith [ hq.2.2.1 lo ( mid + 1 ) ( by linarith ) ( by linarith ) ( by linarith ) ]

/-
PROBLEM
Helper 6: rot_sorted sub-intervals (left)

PROVIDED SOLUTION
Show [lo, mid) is rotated sorted given [lo, hi) is rotated sorted and [mid, hi) is sorted.

Case 1 ([lo, hi) is sorted): [lo, mid) is sorted, hence rot_sorted.

Case 2 ([lo, hi) has pivot q):
- If q ≥ mid: Since [mid, hi) is sorted and [q, hi) is sorted, [mid, q) is part of [lo, q) which is sorted. But actually, q ≥ mid means the pivot is at or after mid. Since [mid, hi) is sorted and contains the pivot (if q > mid), but [mid, hi) is sorted means there's no pivot in [mid, hi)... So q ≤ mid.

Actually: if q ≥ mid, then [q, hi) ⊆ [mid, hi) which is sorted, but also [lo, q) is sorted. If q > mid, then mid is in [lo, q), so arr[lo] < arr[mid] (by [lo, q) sorted if lo < mid). But we also know [mid, hi) is sorted. The issue is whether there can be a pivot in [mid, hi) when [mid, hi) is sorted - no, sorted means no pivot. So all elements in [mid, hi) are increasing. But [lo, q) is sorted too, and arr[hi-1] < arr[lo]. Since arr[q-1] is in [lo, q) and arr[q] is in [q, hi), arr[q-1] > arr[hi-1] ≥ arr[q], so there's a "drop" from q-1 to q. If q > mid, then mid < q, so mid is in [lo, q) and q is in [mid, hi). In [mid, hi) sorted, arr[mid] < arr[q] only if mid < q. But arr[q-1] (in [lo, q), sorted) > arr[q] (since arr[q-1] ≥ arr[lo] > arr[hi-1] ≥ arr[q]). But q-1 and q are adjacent, and arr[q-1] is in the first sorted segment while arr[q] is in the second. Since [mid, hi) is sorted and both q-1 (if q-1 ≥ mid) and q are in [mid, hi), we'd need arr[q-1] < arr[q], contradicting arr[q-1] > arr[q].

So if q > mid and q-1 ≥ mid, then arr[q-1] < arr[q] (by [mid, hi) sorted) but arr[q-1] > arr[hi-1] ≥ arr[q] (by [lo, q) sorted and [q, hi) sorted), contradiction. So q ≤ mid.

With q ≤ mid:
- If q = mid or q < mid: [lo, mid) has pivot at q if q < mid, or [lo, mid) is sorted if q ≥ mid.
  - If q < mid: [lo, q) sorted, [q, mid) ⊆ [q, hi) sorted, arr[mid-1] comes from [q, hi) so arr[q] ≤ arr[mid-1]. arr[lo] > arr[hi-1] ≥ arr[mid-1] (if mid-1 < hi-1) by [q, hi) sorted. So arr[lo] > arr[mid-1] which means arr[hi-1] < arr[lo] translates to something about [lo, mid). We need arr[mid-1]! < arr[lo]! for the rot_sorted of [lo, mid). Since q < mid and arr[q..hi) sorted, arr[q] ≤ arr[mid-1] ≤ arr[hi-1] < arr[lo]. So arr[mid-1] < arr[lo] (since arr[mid-1] ≤ arr[hi-1] < arr[lo]).
  So [lo, mid) has pivot q with [lo, q) sorted, [q, mid) sorted, arr[mid-1] < arr[lo]. ✓
  - If q = mid: [lo, mid) = [lo, q) which is sorted.  ✓
-/
lemma rot_sorted_left_sub (arr : Array ℤ) (lo hi mid : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_hi : mid < hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hright_sorted : subarray_sorted arr mid hi) :
    subarray_rot_sorted arr lo mid := by
  cases hrot;
  · rename_i h;
    exact Or.inl fun i j hi hj hj' => h i j hi hj ( by linarith );
  · rename_i h;
    obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ := h
    by_cases hq6 : q ≤ mid;
    · by_cases hq7 : q = mid;
      · exact Or.inl <| by aesop;
      · refine Or.inr ⟨ q, hq1, lt_of_le_of_ne hq6 hq7, hq3, ?_, ?_ ⟩;
        · exact fun i j hi hj hj' => hq4 i j ( by linarith ) ( by linarith ) ( by omega );
        · refine lt_of_le_of_lt ?_ hq5;
          have hq_le_mid_minus_1 : ∀ i j, q ≤ i → i < j → j < hi → arr[i]! ≤ arr[j]! := by
            exact fun i j hi hj hj' => le_of_lt ( hq4 i j hi hj hj' );
          exact hq_le_mid_minus_1 _ _ ( by omega ) ( by omega ) ( by omega );
    · left;
      intro i j hi hj hj'; exact hq3 i j hi hj ( by linarith ) ;

-- Helper 7: nodup sub-intervals
lemma nodup_sub (arr : Array ℤ) (lo hi lo' hi' : Nat)
    (hnodup : subarray_nodup arr lo hi)
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    subarray_nodup arr lo' hi' :=
  fun i j hi' hj' hlo' hhi' hij => hnodup i j (by omega) (by omega) (by omega) (by omega) hij

/-
PROBLEM
Case A2: sorted left half, target NOT in range → p in right half

PROVIDED SOLUTION
If p ≤ mid, then p ∈ [lo, mid+1). By sorted_target_in_range on [lo, mid+1), arr[lo]! ≤ arr[p]! ≤ arr[mid]!.Since arr[p]! ≠ arr[mid]! (htarget_neq_mid), arr[p]! < arr[mid]!.So arr[lo]! ≤ arr[p]! ∧ arr[p]! < arr[mid]!, contradicting hnot_in_range.Therefore p ≥ mid + 1.

Use by_contra, then derive the contradiction using sorted_target_in_range.
-/
lemma case_A2_p_right (arr : Array ℤ) (lo hi mid p : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_lt : mid < hi)
    (hp : lo ≤ p ∧ p < hi)
    (hleft_sorted : subarray_sorted arr lo (mid + 1))
    (htarget_neq_mid : arr[mid]! ≠ arr[p]!)
    (hnot_in_range : ¬(arr[lo]! ≤ arr[p]! ∧ arr[p]! < arr[mid]!)) :
    mid + 1 ≤ p := by
  by_contra h_contra; push_neg at h_contra; (
  -- By Lemma 3, arr[lo]! ≤ arr[p]! ≤ arr[mid]!.
  have harr_le : arr[lo]! ≤ arr[p]! := by
    exact if h : lo = p then h.symm ▸ le_rfl else hleft_sorted _ _ ( by linarith ) ( lt_of_le_of_ne ( by linarith ) h ) ( by linarith ) |> le_of_lt;
  have harr_le_mid : arr[p]! ≤ arr[mid]! := by
    have := hleft_sorted p mid;
    grind +ring
  have harr_lt_mid : arr[p]! < arr[mid]! := by
    exact lt_of_le_of_ne harr_le_mid htarget_neq_mid.symm
  exact hnot_in_range ⟨harr_le, harr_lt_mid⟩)

/-
PROBLEM
Case B2: sorted right half, target NOT in range → p in left half

PROVIDED SOLUTION
If p ≥ mid, then p ∈ [mid, hi). By sorted_target_in_range on [mid, hi), arr[mid]! ≤ arr[p]! ≤ arr[hi-1]!.Since arr[p]! ≠ arr[mid]! (htarget_neq_mid), arr[p]! > arr[mid]!, so arr[mid]! < arr[p]!.So arr[mid]! < arr[p]! ∧ arr[p]! ≤ arr[hi-1]!, contradicting hnot_in_range.Therefore p < mid.

Use by_contra, then derive the contradiction using sorted_target_in_range.
-/
lemma case_B2_p_left (arr : Array ℤ) (lo hi mid p : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_lt : mid < hi)
    (hp : lo ≤ p ∧ p < hi)
    (hright_sorted : subarray_sorted arr mid hi)
    (htarget_neq_mid : arr[mid]! ≠ arr[p]!)
    (hnot_in_range : ¬(arr[mid]! < arr[p]! ∧ arr[p]! ≤ arr[hi-1]!)) :
    p < mid := by
  -- By contradiction, assume $p \geq \text{mid}$.
  by_contra h_contra;
  -- Since $p \geq mid$, we have $p = mid$ or $mid < p$.
  by_cases hmid_eq_p : p = mid;
  · aesop;
  · -- Since $p > mid$, we have $arr[mid]! < arr[p]!$ by the definition of sorted.
    have hmid_lt_p : arr[mid]! < arr[p]! := by
      exact hright_sorted _ _ ( by linarith ) ( lt_of_le_of_ne ( by linarith ) ( Ne.symm hmid_eq_p ) ) ( by linarith );
    exact hnot_in_range ⟨ hmid_lt_p, by linarith [ sorted_target_in_range arr mid hi p hmid_lt ( by omega ) hright_sorted ] ⟩

/-
PROBLEM
Case A1: sorted left half, target in range → p in left half

PROVIDED SOLUTION
Need to show p < mid given arr[lo]! ≤ arr[p]! < arr[mid]! and [lo, mid+1) sorted and [lo, hi) rot_sorted.

If p ≥ mid+1 (p ∈ [mid+1, hi)):
Consider the rotated sorted structure of [lo, hi):
Case sorted: [lo, hi) sorted implies [mid+1, hi) sorted with arr[mid+1]! > arr[mid]! > arr[p]! (since target < arr[mid]). But arr[p]! (at position p ≥ mid+1) must be ≥ arr[mid+1]! (sorted), giving arr[p]! ≥ arr[mid+1]! > arr[mid]! > arr[p]!. Contradiction.

Case pivot q:
  If q ≤ mid+1: [mid+1, hi) ⊆ [q, hi) sorted. All elements in [q, hi) ≤ arr[hi-1]! < arr[lo]!. So arr[p]! ≤ arr[hi-1]! < arr[lo]! ≤ arr[p]! (by hin_range.1). So arr[p]! < arr[p]!. Contradiction.
  If q > mid+1: Elements in [mid+1, q) ⊆ [lo, q) sorted, so arr[mid+1]! > arr[mid]! > arr[p]!. But p ∈ [mid+1, q) means arr[p]! ≥ arr[mid+1]! (sorted in [lo, q)), contradiction. If p ∈ [q, hi): arr[p]! ≤ arr[hi-1]! < arr[lo]! ≤ arr[p]!, contradiction.

If p = mid: arr[mid]! = arr[p]!, contradicting htarget_neq_mid.

So p < mid.
-/
lemma case_A1_p_left (arr : Array ℤ) (lo hi mid p : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_lt : mid < hi)
    (hp : lo ≤ p ∧ p < hi)
    (hnodup : subarray_nodup arr lo hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hleft_sorted : subarray_sorted arr lo (mid + 1))
    (htarget_neq_mid : arr[mid]! ≠ arr[p]!)
    (hin_range : arr[lo]! ≤ arr[p]! ∧ arr[p]! < arr[mid]!) :
    p < mid := by
  -- By contradiction, assume $p \geq \text{mid} + 1$.
  by_contra h_contra
  have h_ge : p ≥ mid + 1 := by
    cases lt_or_eq_of_le ( le_of_not_gt h_contra ) <;> aesop;
  obtain ⟨q, hq⟩ : ∃ q, lo < q ∧ q < hi ∧ subarray_sorted arr lo q ∧ subarray_sorted arr q hi ∧ arr[hi-1]! < arr[lo]! := by
    cases' hrot with hrot_left hrot_right;
    · have := hrot_left mid p ( by linarith ) ( by linarith ) ( by linarith ) ; linarith;
    · exact hrot_right;
  by_cases hq_le_p : q ≤ p;
  · linarith [ sorted_target_in_range arr q hi p ( by linarith ) ⟨ by linarith, by linarith ⟩ hq.2.2.2.1 ];
  · have := hq.2.2.1 mid p ( by linarith ) ( by linarith ) ( by linarith ) ; linarith;

/-
PROBLEM
Case B1: sorted right half, target in range → p in right half

PROVIDED SOLUTION
Need to show p ≥ mid+1 given arr[mid]! < arr[p]! ≤ arr[hi-1]! and [mid, hi) sorted and [lo, hi) rot_sorted.

If p ≤ mid-1 (p < mid, i.e. p ∈ [lo, mid)):
Consider the rotated sorted structure of [lo, hi):
Case sorted: Impossible since arr[lo]! > arr[mid]! (from the context where case B applies).

Case pivot q:
  If q ≤ mid: [lo, q) sorted. If p < q: arr[p]! ≤ arr[q-1]!. [lo, q) sorted so arr[q-1]! < ... arr[lo]!. Actually arr[q-1]! is the max of [lo, q). And all elements in [q, hi) are < arr[lo]! (by arr[hi-1]! < arr[lo]! and [q, hi) sorted). But target > arr[mid]! and arr[mid]! ∈ [q, hi) (since q ≤ mid). [mid, hi) sorted so arr[mid]! ≥ arr[q]!. Also arr[hi-1]! ≥ target = arr[p]!.
  If p ∈ [lo, q): arr[p]! is in [lo, q) sorted, so arr[p]! ≥ arr[lo]! > arr[hi-1]! ≥ target = arr[p]!. Contradiction (arr[p]! > arr[p]!).
  If p ∈ [q, mid): then p ∈ [q, hi) sorted, so arr[p]! ≤ arr[mid-1]! < arr[mid]! (sorted in [q, hi) or [mid, hi)). But target > arr[mid]! > arr[p]!. But arr[p]! = target. Contradiction.

  If q > mid: then [lo, q) sorted ⊇ [lo, mid+1), so arr[lo] < arr[mid] (lo < mid in sorted). But arr[lo] > arr[mid] (case B context). Contradiction.

If p = mid: arr[mid]! = arr[p]!, contradicting htarget_neq_mid.

So p ≥ mid + 1.
-/
lemma case_B1_p_right (arr : Array ℤ) (lo hi mid p : Nat)
    (hlo : lo < hi) (hmid_lo : lo ≤ mid) (hmid_lt : mid < hi)
    (hp : lo ≤ p ∧ p < hi)
    (hnodup : subarray_nodup arr lo hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hright_sorted : subarray_sorted arr mid hi)
    (htarget_neq_mid : arr[mid]! ≠ arr[p]!)
    (hin_range : arr[mid]! < arr[p]! ∧ arr[p]! ≤ arr[hi-1]!) :
    mid + 1 ≤ p := by
  -- Since the right half is sorted, if $p < mid$, then $arr[p]! < arr[mid]!$, contradicting $arr[mid]! < arr[p]!$.
  by_contra h_contra
  have h_p_lt_mid : p < mid := by
    grind;
  obtain ⟨q, hq⟩ : ∃ q, lo < q ∧ q < hi ∧ subarray_sorted arr lo q ∧ subarray_sorted arr q hi ∧ arr[hi-1]! < arr[lo]! := by
    cases hrot;
    · rename_i h;
      linarith [ h p mid ( by linarith ) ( by linarith ) ( by linarith ) ];
    · tauto;
  -- Since $p < mid$, we have $p \in [lo, q)$ or $p \in [q, mid)$.
  by_cases hpq : p < q;
  · have := hq.2.2.1 ( lo : ℕ ) p; simp_all +decide ;
    grind;
  · linarith [ hq.2.2.2.1 p mid ( by linarith ) ( by linarith ) ( by linarith ) ]

/-
PROBLEM
Main completeness lemma

PROVIDED SOLUTION
Prove by strong induction on (hi - lo).

Unfold myBs2. If lo ≥ hi, contradiction with hp.

If lo < hi:
  mid = lo + (hi-lo)/2. We have lo ≤ mid < hi.

  If arr[mid]! = target: Since arr[mid]! = target = arr[p]!, by hnodup (since mid and p are both in [lo, hi)), mid = p. Done.

  If arr[mid]! ≠ target:
    Case arr[lo]! ≤ arr[mid]!:
      Have hleft := rot_sorted_left_sorted ... : sorted [lo, mid+1)
      If arr[lo]! ≤ target ∧ target < arr[mid]!:
        By case_A1_p_left, p < mid. Apply IH on [lo, mid) with:
        - rot_sorted: rot_sorted_left_sub ... (using rot_sorted_right_sorted for [mid, hi) sorted... but we're in case arr[lo] ≤ arr[mid], so rot_sorted_right_sorted doesn't apply directly. Use rot_sorted_left_sub with [mid, hi) sorted? No, that needs arr[lo] > arr[mid].

        Actually, for [lo, mid), use: the left sub is rot_sorted. Since [lo, mid+1) is sorted, [lo, mid) is sorted (sub-interval of sorted). So subarray_rot_sorted [lo, mid) is Or.inl (sorted).
      Else:
        By case_A2_p_right, p ≥ mid+1. Apply IH on [mid+1, hi) with:
        - rot_sorted: rot_sorted_right_sub ...

    Case arr[lo]! > arr[mid]!:
      Have hright := rot_sorted_right_sorted ... : sorted [mid, hi)
      If arr[mid]! < target ∧ target ≤ arr[hi-1]!:
        By case_B1_p_right, p ≥ mid+1. Apply IH on [mid+1, hi) with:
        - rot_sorted: [mid+1, hi) is sorted (sub-interval of [mid, hi) sorted). So Or.inl.
      Else:
        By case_B2_p_left, p < mid. Apply IH on [lo, mid) with:
        - rot_sorted: rot_sorted_left_sub ...

Key: use the helpers to determine which sub-interval p belongs to, and use rot_sorted_left_sub/rot_sorted_right_sub/Or.inl for the sub-interval's rot_sorted property. Use nodup_sub for nodup.
-/
set_option maxHeartbeats 3200000 in
lemma myBs2_complete (target : ℤ) (arr : Array ℤ) (lo hi p : Nat)
    (hhi : hi ≤ arr.size)
    (hnodup : subarray_nodup arr lo hi)
    (hrot : subarray_rot_sorted arr lo hi)
    (hp : lo ≤ p ∧ p < hi)
    (htarget : arr[p]! = target) :
    myBs2 target arr lo hi = Int.ofNat p := by
  revert p;
  intro p hp htarget
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi p;
  by_cases hlo_lt_hi : lo < hi;
  · -- Let's denote the middle index as `mid`.
    set mid := lo + (hi - lo) / 2;
    by_cases hmid : arr[mid]! = target;
    · have hmid_eq_p : mid = p := by
        apply hnodup;
        · exact Nat.le_add_right _ _;
        · omega;
        · linarith;
        · grind;
        · rw [hmid, htarget];
      unfold myBs2; aesop;
    · by_cases hle : arr[lo]! ≤ arr[mid]!;
      · by_cases hcase : arr[lo]! ≤ target ∧ target < arr[mid]!;
        · -- By case_A1_p_left, we have p < mid.
          have hp_lt_mid : p < mid := by
            apply case_A1_p_left arr lo hi mid p hlo_lt_hi (by
            exact Nat.le_add_right _ _) (by
            omega) hp hnodup hrot (rot_sorted_left_sorted arr lo hi mid hlo_lt_hi (by
            exact Nat.le_add_right _ _) (by
            omega) hnodup hrot hle) (by
            grind) (by
            aesop);
          -- Apply the induction hypothesis to the left half [lo, mid).
          have h_ind_left : myBs2 target arr lo (mid) = Int.ofNat p := by
            apply ih (mid - lo);
            any_goals omega;
            · exact nodup_sub arr lo hi lo mid hnodup ( by linarith ) ( by omega );
            · apply rot_sorted_left_sub;
              any_goals exact mid + 1;
              · omega;
              · exact Nat.le_add_right _ _;
              · norm_num;
              · apply Or.inl;
                apply rot_sorted_left_sorted;
                any_goals exact hlo_lt_hi.trans_le ( Nat.le_refl _ );
                · exact Nat.le_add_right _ _;
                · omega;
                · assumption;
                · assumption;
                · linarith;
              · exact fun i j hi hj hj' => by linarith;
          unfold myBs2; aesop;
        · -- Since $p \geq mid + 1$, we can apply the induction hypothesis to the right half.
          have h_ind_right : myBs2 target arr (mid + 1) hi = Int.ofNat p := by
            apply ih (hi - (mid + 1));
            any_goals omega;
            · exact nodup_sub arr lo hi ( mid + 1 ) hi hnodup ( by omega ) ( by omega );
            · apply rot_sorted_right_sub;
              exact?;
              · exact Nat.le_add_right _ _;
              · omega;
              · assumption;
              · apply rot_sorted_left_sorted;
                any_goals exact mid + 1;
                any_goals omega;
                · apply nodup_sub;
                  exact hnodup;
                  · linarith;
                  · omega;
                · exact Or.inl <| rot_sorted_left_sorted arr lo hi mid hlo_lt_hi ( by omega ) ( by omega ) hnodup hrot hle;
            · exact ⟨ case_A2_p_right arr lo hi mid p hlo_lt_hi ( by omega ) ( by omega ) hp ( rot_sorted_left_sorted arr lo hi mid hlo_lt_hi ( by omega ) ( by omega ) hnodup hrot hle ) ( by aesop ) ( by aesop ), hp.2 ⟩;
          unfold myBs2; aesop;
      · -- Since `arr[lo]! > arr[mid]!`, the right half `[mid, hi)` is sorted.
        have hright_sorted : subarray_sorted arr mid hi := by
          apply rot_sorted_right_sorted arr lo hi mid hlo_lt_hi (by
          exact Nat.le_add_right _ _) (by
          omega) hnodup hrot (by
          exact not_le.mp hle);
        by_cases hmid_lt_p : arr[mid]! < target ∧ target ≤ arr[hi-1]!;
        · -- Since `arr[mid]! < target ∧ target ≤ arr[hi-1]!`, we have `p ≥ mid + 1`.
          have hp_ge_mid_plus_1 : mid + 1 ≤ p := by
            apply case_B1_p_right;
            all_goals omega;
          -- Apply the induction hypothesis to the right half `[mid + 1, hi)`.
          have h_ind_right : myBs2 target arr (mid + 1) hi = Int.ofNat p := by
            apply ih (hi - (mid + 1));
            any_goals omega;
            · apply nodup_sub;
              exact hnodup;
              · omega;
              · grind;
            · exact Or.inl <| fun i j hi hj hj' => hright_sorted i j ( by omega ) ( by omega ) ( by omega );
          unfold myBs2; aesop;
        · -- Since `arr[mid]! ≥ target` or `target > arr[hi-1]!`, we have `p < mid`.
          have hp_lt_mid : p < mid := by
            apply case_B2_p_left arr lo hi mid p hlo_lt_hi (by
            exact Nat.le_add_right _ _) (by
            omega) hp hright_sorted (by
            aesop) (by
            grind);
          -- Apply the induction hypothesis to the left half `[lo, mid)`.
          have h_ind_left : myBs2 target arr lo mid = Int.ofNat p := by
            apply ih (mid - lo);
            any_goals omega;
            · exact nodup_sub arr lo hi lo mid hnodup ( by linarith ) ( by omega );
            · apply rot_sorted_left_sub;
              any_goals assumption;
              · exact Nat.le_add_right _ _;
              · omega;
          rw [ ← h_ind_left, myBs2 ];
          grind;
  · grind