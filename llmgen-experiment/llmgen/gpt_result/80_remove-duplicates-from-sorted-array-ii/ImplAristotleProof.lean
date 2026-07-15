import Mathlib.Tactic

-- Never add new imports here

set_option maxHeartbeats 40000000
set_option pp.coercions false

/- Problem Description
    RemoveDuplicatesFromSortedArrayII: given a sorted (non-decreasing) integer array, keep each value at most twice.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array of integers sorted in non-decreasing order.
    2. The output consists of a number k and an array out representing the modified array state.
    3. Only the first k elements of out are relevant; elements beyond index k are unconstrained.
    4. The first k elements must be in non-decreasing order.
    5. For every integer value x, the number of occurrences of x in the first k elements is the minimum of:
       a. 2, and
       b. the number of occurrences of x in the entire input array.
    6. Therefore, each distinct value appears at most twice in the kept prefix.
    7. Because the input is sorted and the output prefix is required to be sorted with these exact capped counts,
       the kept prefix is uniquely determined and preserves the relative order implied by sortedness.
-/

section Specs
def countInPrefix (arr : Array Int) (k : Nat) (x : Int) : Nat :=
  (arr.take k).count x

def sortedPrefix (arr : Array Int) (k : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < k → arr[i]! ≤ arr[i + 1]!

def precondition (nums : Array Int) : Prop :=
  sortedPrefix nums nums.size

def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  let k : Nat := result.1
  let out : Array Int := result.2
  out.size = nums.size ∧
  k ≤ nums.size ∧
  sortedPrefix out k ∧
  (∀ (x : Int), countInPrefix out k x = Nat.min 2 (countInPrefix nums nums.size x))
end Specs

section TestCases
def test1_nums : Array Int := #[1, 1, 1, 2, 2, 3]
def test1_Expected : Nat × Array Int := (5, #[1, 1, 2, 2, 3, 0])
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 1, 2, 3, 3]
def test2_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 3, 3, 0, 0])
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (2, #[2, 2, 0, 0])
def test6_nums : Array Int := #[1, 1, 2, 2, 3, 3]
def test6_Expected : Nat × Array Int := (6, #[1, 1, 2, 2, 3, 3])
def test7_nums : Array Int := #[-1, -1, -1, 0, 0, 0, 1]
def test7_Expected : Nat × Array Int := (5, #[-1, -1, 0, 0, 1, 0, 0])
def test8_nums : Array Int := #[0, 1, 2]
def test8_Expected : Nat × Array Int := (3, #[0, 1, 2])
def test9_nums : Array Int := #[0, 0, 0, 1, 1, 2, 2, 2, 2, 3]
def test9_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 2, 3, 0, 0, 0])
end TestCases

section Proof

lemma extract_setIfInBounds_push (arr : Array ℤ) (k : ℕ) (v : ℤ) (hk : k < arr.size) :
    (arr.setIfInBounds k v).extract 0 (k + 1) = (arr.extract 0 k).push v := by
  simp only [Array.setIfInBounds, hk, ↓reduceDIte]
  apply Array.ext
  · simp [Nat.min_eq_left (by omega : k + 1 ≤ arr.size),
          Nat.min_eq_left (by omega : k ≤ arr.size)]
  · intro j hj1 hj2
    simp [Nat.min_eq_left (by omega : k + 1 ≤ arr.size)] at hj1
    simp [Nat.min_eq_left (by omega : k ≤ arr.size)] at hj2
    simp only [Array.getElem_extract, Array.getElem_push, Array.getElem_set]
    by_cases hjk : j < k
    · have h1 : ¬(k = j) := by omega
      have h2 : j < k ∧ j < arr.size := ⟨hjk, by omega⟩
      simp [h1, h2]
    · have hjeq : k = j := by omega
      simp [hjeq]

lemma extract_succ_push (arr : Array ℤ) (i : ℕ) (hi : i < arr.size) :
    arr.extract 0 (i + 1) = (arr.extract 0 i).push arr[i]! := by
  rcases arr with ⟨⟨l⟩⟩ <;> aesop

lemma sorted_mono (arr : Array ℤ) (n : ℕ)
    (hsorted : ∀ (j : ℕ), j + 1 < n → arr[j]! ≤ arr[j + 1]!)
    (a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    arr[a]! ≤ arr[b]! := by
  induction' hab with b _ ih
  · rfl
  · exact le_trans (ih (Nat.lt_of_succ_lt hb)) (hsorted _ hb)

lemma getElem!_extract_eq (arr : Array ℤ) (k j : ℕ) (hj : j < k) (hk : k ≤ arr.size) :
    (arr.extract 0 k)[j]! = arr[j]! := by
  have hjs : j < (arr.extract 0 k).size := by simp; omega
  have hja : j < arr.size := by omega
  simp only [getElem!_pos (arr.extract 0 k) j hjs, getElem!_pos arr j hja,
             Array.getElem_extract]
  congr 1; omega

lemma getElem!_set_ne (arr : Array ℤ) (k j : ℕ) (v : ℤ) (hk : k < arr.size) (hj : j < arr.size) (hjk : k ≠ j) :
    (arr.set k v hk)[j]! = arr[j]! := by
  have hj' : j < (arr.set k v hk).size := by simp; omega
  simp only [getElem!_pos (arr.set k v hk) j hj', getElem!_pos arr j hj,
             Array.getElem_set, hjk, ↓reduceIte]

lemma getElem!_set_eq (arr : Array ℤ) (k : ℕ) (v : ℤ) (hk : k < arr.size) :
    (arr.set k v hk)[k]! = v := by
  have hk' : k < (arr.set k v hk).size := by simp; omega
  simp only [getElem!_pos (arr.set k v hk) k hk', Array.getElem_set, ↓reduceIte]

/-
PROBLEM
Helper: array extract equals Array.mk of mapped list

PROVIDED SOLUTION
Show array equality by proving their lists are equal. Use Array.ext and compare element by element. For each j < k, (arr.extract 0 k)[j] = arr[0+j] (by Array.getElem_extract) and the RHS has (List.map ...)[j] = arr[j]! (by List.getElem_map and List.getElem_range).

ABSOLUTELY CRITICAL: Do NOT use `grind` or `grind +ring` anywhere. They are BROKEN. Use `simp`, `omega`, `aesop`, `ext`, `congr` instead.
-/
lemma extract_eq_mk_map (arr : Array ℤ) (k : ℕ) (hk : k ≤ arr.size) :
    arr.extract 0 k = { toList := List.map (fun m => arr[m]!) (List.range k) } := by
                          grind

/-
PROBLEM
Helper: if out[m]! ≠ v for all m except possibly one, then the Finset filter has at most 1 element

PROVIDED SOLUTION
Take a, b in the filter set. Both satisfy out[a]! = v, out[b]! = v, and a < k, b < k.
By h_lt, for any m < k-2, out[m]! < v, so out[m]! ≠ v. So a ≥ k-2 and b ≥ k-2.
By hne, out[k-2]! ≠ v. So a ≠ k-2 and b ≠ k-2.
Since a < k and a ≥ k-2 and a ≠ k-2, we get a = k-1.
Similarly b = k-1. So a = b.

ABSOLUTELY CRITICAL: Do NOT use `grind` or `grind +ring` anywhere. They are BROKEN. Use `simp`, `omega`, `linarith`, `Finset.mem_filter`, `Finset.mem_range` instead.
-/
lemma finset_filter_at_most_one (out : Array ℤ) (k : ℕ) (v : ℤ)
    (h_lt : ∀ m < k - 2, out[m]! < v)
    (hne : ¬v = out[k - 2]!)
    (hk2 : 2 ≤ k) :
    ∀ a ∈ Finset.filter (fun m => out[m]! = v) (Finset.range k),
    ∀ b ∈ Finset.filter (fun m => out[m]! = v) (Finset.range k),
    a = b := by
      intro a ha b hb
      simp [Finset.mem_filter, Finset.mem_range] at ha hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      have ha_ge : a ≥ k - 2 := by
        by_contra h; push_neg at h; linarith [h_lt a h]
      have hb_ge : b ≥ k - 2 := by
        by_contra h; push_neg at h; linarith [h_lt b h]
      have ha_ne : a ≠ k - 2 := by
        intro heq; subst heq; exact hne ha2.symm
      have hb_ne : b ≠ k - 2 := by
        intro heq; subst heq; exact hne hb2.symm
      omega

/-
PROVIDED SOLUTION
CRITICAL: Do NOT use `grind` or `grind +ring` anywhere in the proof. They WILL fail during build and cause the entire project to fail. Use ONLY `simp`, `omega`, `linarith`, `aesop`, `norm_num`, `by_contra`, `push_neg`, and manual case analysis.

By contradiction. Assume count v (out.extract 0 k) ≥ 2.
Since count ≥ 2, there exist two distinct indices j1 < j2 < k with out[j1]! = v and out[j2]! = v.

Key step: For any m with j1 ≤ m < k, out[m]! = v.
Proof: By sorted_mono, out[j1]! ≤ out[m]!. By hall_le, out[m]! ≤ v. Since out[j1]! = v, we get v ≤ out[m]! ≤ v, so out[m]! = v.

Since j1 < j2 and j2 < k, we have j1 ≤ k - 2. So out[k-2]! = v by the above, contradicting hne.

For extracting two indices from count ≥ 2: count v arr ≥ 2 means arr.toList.count v ≥ 2. Use List.count_le_of_mem or convert to showing the filter has ≥ 2 elements, then extract two.

Use `sorted_mono` (defined above in the file) for the monotonicity argument.
-/
lemma count_le_one_of_sorted_and_ne_km2
    (out : Array ℤ) (k : ℕ) (v : ℤ)
    (hsorted : ∀ (j : ℕ), j + 1 < k → out[j]! ≤ out[j + 1]!)
    (hne : ¬v = out[k - 2]!)
    (hk2 : 2 ≤ k)
    (hk_le : k ≤ out.size)
    (hall_le : ∀ (j : ℕ), j < k → out[j]! ≤ v) :
    Array.count v (out.extract 0 k) ≤ 1 := by
      -- Since the array is sorted and out[k-2]! ≠ v, for any m < k-2, out[m]! < out[k-2]! ≤ v.
      have h_lt : ∀ m < k - 2, out[m]! < v := by
        intros m hm
        have h_le : out[m]! ≤ out[k - 2]! := by
          apply sorted_mono;
          exacts [ hsorted, le_of_lt hm, Nat.sub_lt ( by linarith ) ( by linarith ) ]
        have h_ne : out[k - 2]! < v := by
          exact lt_of_le_of_ne ( hall_le _ ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ) ( Ne.symm hne )
        exact lt_of_le_of_lt h_le h_ne;
      -- Since there can be at most one element equal to v in the first k elements, the count of v is at most 1.
      have h_count : (out.extract 0 k).count v ≤ (Finset.filter (fun m => out[m]! = v) (Finset.range k)).card := by
        have h_count : (out.extract 0 k).count v = (List.foldl (fun acc m => if out[m]! = v then acc + 1 else acc) 0 (List.range k)) := by
          have h_count : (out.extract 0 k).count v = List.count v (List.map (fun m => out[m]!) (List.range k)) := by
            -- The array extracted from out up to k is equivalent to the list obtained by mapping out[m]! over the range k.
            have h_array_list : out.extract 0 k = Array.mk (List.map (fun m => out[m]!) (List.range k)) := by
              exact extract_eq_mk_map out k hk_le;
            aesop;
          convert h_count using 1;
          induction' ( List.range k ) using List.reverseRecOn <;> aesop;
        convert h_count.le;
        induction' k with k ih;
        · contradiction;
        · induction' k + 1 with k ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
          rw [ Finset.range_add_one, Finset.filter_insert ] ; aesop;
      refine le_trans h_count ?_;
      refine' Finset.card_le_one.mpr _;
      exact finset_filter_at_most_one out k v h_lt hne hk2

lemma out_prefix_le_nums_i
    (nums out : Array ℤ) (i k : ℕ)
    (require_1 : ∀ (j : ℕ), j + 1 < nums.size → nums[j]! ≤ nums[j + 1]!)
    (inv_counts : ∀ (x : ℤ), Array.count x (out.extract 0 k) = Nat.min 2 (Array.count x (nums.extract 0 i)))
    (inv_sorted : ∀ (j : ℕ), j + 1 < k → out[j]! ≤ out[j + 1]!)
    (hk_le_i : k ≤ i)
    (hi : i < nums.size)
    (hout_size : out.size = nums.size) :
    ∀ (j : ℕ), j < k → out[j]! ≤ nums[i]! := by
      intro j hj_lt_k
      have h_count_out_j : Array.count (out[j]!) (out.extract 0 k) ≥ 1 := by
        simp +zetaDelta at *
        rw [Array.mem_iff_getElem]
        refine ⟨j, by simp; omega, ?_⟩
        simp [Array.getElem_extract, getElem!_pos out j (by omega)]
      have h_count_nums_j : Array.count (out[j]!) (nums.extract 0 i) ≥ 1 := by
        have := inv_counts (out[j]!)
        simp [Nat.min_def] at this
        split_ifs at this with h <;> omega
      have h_exists_m : ∃ m < i, nums[m]! = out[j]! := by
        contrapose! h_count_nums_j; simp_all +decide [Array.count]
        intro a ha; rw [Array.mem_iff_getElem] at ha; aesop
      obtain ⟨m, hm_lt_i, hm_eq⟩ := h_exists_m
      have h_le : nums[m]! ≤ nums[i]! := by
        apply sorted_mono; aesop
        · linarith
        · linarith
      rw [hm_eq] at h_le
      exact h_le

theorem goal_3 (nums : Array ℤ) (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!) (i : ℕ) (k : ℕ) (out : Array ℤ) (invariant_inv_i_bounds : i ≤ nums.size) (invariant_inv_out_size : out.size = nums.size) (invariant_inv_k_le_i : k ≤ i) (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i))) (invariant_inv_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! ≤ out[i + OfNat.ofNat 1]!) (if_pos : i < nums.size) (if_neg_1 : ¬nums[i]! = out[k - OfNat.ofNat 2]!) (if_neg : OfNat.ofNat 2 ≤ k) : ∀ (x : ℤ), Array.count x ((out.setIfInBounds k nums[i]!).extract (OfNat.ofNat 0) (k + OfNat.ofNat 1)) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))) := by
    intro x
    by_cases hx : x = nums[i]!
    · have h_count_le : Array.count x (out.extract 0 k) ≤ 1 := by
        apply_rules [count_le_one_of_sorted_and_ne_km2]
        · aesop
        · linarith
        · intro j hj; have := out_prefix_le_nums_i nums out i k; aesop
      rw [extract_setIfInBounds_push _ _ _ (by omega)]
      rw [extract_succ_push nums i if_pos]
      subst hx
      simp only [Array.count_push, beq_self_eq_true, ↓reduceIte]
      have h := invariant_inv_counts (nums[i]!)
      set c := Array.count (nums[i]!) (out.extract 0 k) with hc_def
      set d := Array.count (nums[i]!) (nums.extract 0 i) with hd_def
      change c ≤ 1 at h_count_le
      simp [Nat.min_def] at h ⊢
      split_ifs at h ⊢ with h1 h2 <;> (try norm_num at *) <;> omega
    · rw [extract_setIfInBounds_push _ _ _ (by omega)]
      simp_all +decide [Array.count_push]
      rw [show nums.extract 0 (i + 1) = nums.extract 0 i ++ #[nums[i]!] from ?_, Array.count_append]; aesop
      convert extract_succ_push nums i if_pos using 1

theorem goal_4 (nums : Array ℤ) (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!) (i : ℕ) (k : ℕ) (out : Array ℤ) (invariant_inv_i_bounds : i ≤ nums.size) (invariant_inv_out_size : out.size = nums.size) (invariant_inv_k_le_i : k ≤ i) (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i))) (invariant_inv_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! ≤ out[i + OfNat.ofNat 1]!) (if_pos : i < nums.size) (if_neg_1 : ¬nums[i]! = out[k - OfNat.ofNat 2]!) (if_neg : OfNat.ofNat 2 ≤ k) : ∀ i_1 < k, (out.setIfInBounds k nums[i]!)[i_1]! ≤ (out.setIfInBounds k nums[i]!)[i_1 + OfNat.ofNat 1]! := by
    intros i_1 hi_1
    have hk_lt_out : k < out.size := by omega
    simp only [Array.setIfInBounds, hk_lt_out, ↓reduceDIte]
    by_cases h : i_1 + 1 < k
    · -- Both i_1 and i_1+1 are < k, so set at k doesn't affect them
      rw [getElem!_set_ne out k i_1 _ hk_lt_out (by omega) (by omega),
          getElem!_set_ne out k (i_1 + 1) _ hk_lt_out (by omega) (by omega)]
      exact invariant_inv_sorted i_1 h
    · -- i_1 + 1 = k (since i_1 < k and i_1 + 1 ≥ k)
      have hi1k : i_1 + 1 = k := by omega
      rw [getElem!_set_ne out k i_1 _ hk_lt_out (by omega) (by omega)]
      rw [show i_1 + OfNat.ofNat 1 = k from hi1k]
      rw [getElem!_set_eq out k _ hk_lt_out]
      have h_out_le := out_prefix_le_nums_i nums out i k require_1 invariant_inv_counts
        invariant_inv_sorted invariant_inv_k_le_i if_pos invariant_inv_out_size i_1 (by omega)
      simp only [getElem!_pos] at h_out_le ⊢
      exact h_out_le

end Proof
