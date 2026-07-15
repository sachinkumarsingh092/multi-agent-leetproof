import Mathlib.Tactic

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    RemoveDuplicatesFromSortedArray: Remove duplicates from a sorted integer array in-place and return the number of unique elements.
    Natural language breakdown:
    1. The input is an array of integers `nums` that is sorted in non-decreasing order.
    2. We return a natural number `k` that equals the number of distinct values appearing in `nums`.
    3. We also return an output array `out` of the same size as `nums`.
    4. The first `k` elements of `out` contain each distinct value from `nums` exactly once.
    5. These first `k` elements are in the same order as they appear in `nums` (stability).
    6. Since `nums` is sorted, the `out` prefix of length `k` is strictly increasing.
    7. Elements of `out` at indices ≥ k are unspecified and can be ignored.
    8. Edge cases: empty array (k = 0), singleton (k = 1), all equal (k = 1), already strictly increasing (k = nums.size).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: sorted (non-decreasing) predicate on arrays, phrased with Nat indices.
def ArraySortedLe (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Helper: prefix is strictly increasing (hence no duplicates in the prefix).
def PrefixStrictIncreasing (a : Array Int) (k : Nat) : Prop :=
  k ≤ a.size ∧ ∀ (i : Nat), i + 1 < k → a[i]! < a[i + 1]!

-- Helper: membership agreement between input and the produced unique prefix.
-- Every value appearing anywhere in nums appears in the first k cells of out, and vice-versa.
def PrefixSameMembers (nums : Array Int) (k : Nat) (out : Array Int) : Prop :=
  k ≤ out.size ∧
    ∀ (x : Int), x ∈ nums ↔ (∃ (i : Nat), i < k ∧ out[i]! = x)

-- Helper: stability/order. There exists a strictly increasing index map f selecting the prefix
-- elements from nums in order. Additionally, each selected index is the first occurrence of that value.
def PrefixOccursInOrderFirst (nums : Array Int) (out : Array Int) (k : Nat) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), i < k → f i < nums.size ∧ out[i]! = nums[f i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < k → f i < f j) ∧
    (∀ (i : Nat), i < k → ∀ (j : Nat), j < f i → nums[j]! ≠ out[i]!)

-- Precondition: input is sorted in non-decreasing order.
def precondition (nums : Array Int) : Prop :=
  ArraySortedLe nums

-- Postcondition: result k is the number of unique elements; out is same size as nums;
-- first k positions are unique values in stable order; rest is irrelevant.
def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  result.snd.size = nums.size ∧
    PrefixStrictIncreasing result.snd result.fst ∧
    PrefixSameMembers nums result.fst result.snd ∧
    PrefixOccursInOrderFirst nums result.snd result.fst
end Specs

section TestCases
-- Test case 1: Example 1
-- Input: nums = [1,1,2]
-- Output: k = 2, prefix = [1,2]
def test1_nums : Array Int := #[1, 1, 2]
def test1_Expected : Nat × Array Int := (2, #[1, 2, 0])

-- Test case 2: Example 2
-- Input: nums = [0,0,1,1,1,2,2,3,3,4]
-- Output: k = 5, prefix = [0,1,2,3,4]
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
def test2_Expected : Nat × Array Int := (5, #[0, 1, 2, 3, 4, 0, 0, 0, 0, 0])

-- Test case 3: Empty array
-- Output: k = 0, out empty
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])

-- Test case 4: Singleton array
-- Output: k = 1, prefix = [7]
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])

-- Test case 5: All equal elements
-- Output: k = 1, prefix = [2]
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (1, #[2, 0, 0, 0])

-- Test case 6: Already strictly increasing
-- Output: k = size, out may equal input
def test6_nums : Array Int := #[1, 2, 3, 4]
def test6_Expected : Nat × Array Int := (4, #[1, 2, 3, 4])

-- Test case 7: Includes negative values and duplicates
-- Input: [-3,-3,-1,-1,0,2,2] -> uniques [-3,-1,0,2]
def test7_nums : Array Int := #[-3, -3, -1, -1, 0, 2, 2]
def test7_Expected : Nat × Array Int := (4, #[-3, -1, 0, 2, 0, 0, 0])

-- Test case 8: Duplicates at the beginning only
-- Input: [0,0,0,1,2,3] -> uniques [0,1,2,3]
def test8_nums : Array Int := #[0, 0, 0, 1, 2, 3]
def test8_Expected : Nat × Array Int := (4, #[0, 1, 2, 3, 0, 0])

-- Test case 9: Duplicates at the end only
-- Input: [1,2,3,4,4,4] -> uniques [1,2,3,4]
def test9_nums : Array Int := #[1, 2, 3, 4, 4, 4]
def test9_Expected : Nat × Array Int := (4, #[1, 2, 3, 4, 0, 0])

-- Recommend to validate: precondition, postcondition, RemoveDuplicatesFromSortedArray
end TestCases

section Proof

/-
PROVIDED SOLUTION
The goal is to show that after doing setIfInBounds on index j (which is >= i_2), the prefix of length i_2 still covers all nums values. Since j >= i_2, and we're only looking at indices q < i_2, the setIfInBounds at index j doesn't affect any element at index q < i_2 (since i_2 <= j). So (out_2.setIfInBounds j 0)[q]! = out_2[q]! for q < i_2. Then use invariant_nums_covered2 which gives exactly what we need for out_2.
-/
theorem goal_8 (nums : Array ℤ) (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!) (i_1 : ℕ) (i_2 : ℕ) (out_1 : Array ℤ) (j : ℕ) (out_2 : Array ℤ) (invariant_j_lower2 : i_2 ≤ j) (invariant_j_upper2 : j ≤ out_2.size) (invariant_out_size2 : out_2.size = nums.size) (a : OfNat.ofNat 1 ≤ i_2) (a_1 : i_2 ≤ nums.size) (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!) (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_2[q]!) (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_2[p]! = nums[q]!) (invariant_k_le_out2 : i_2 ≤ out_2.size) (if_pos : j < out_2.size) (invariant_i_lower : OfNat.ofNat 1 ≤ i_1) (invariant_i_upper : i_1 ≤ nums.size) (invariant_k_lower : OfNat.ofNat 1 ≤ i_2) (invariant_k_upper : i_2 ≤ i_1) (invariant_out_size : out_1.size = nums.size) (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!) (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!) (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!) (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!) (if_neg : ¬nums = #[]) (done_1 : nums.size ≤ i_1) (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!) : ∀ p < nums.size, ∃ q < i_2, nums[p]! = (out_2.setIfInBounds j (OfNat.ofNat 0))[q]! := by
    -- Apply the invariant_nums_covered2 to obtain the q.
    intro p hp
    obtain ⟨q, hq₁, hq₂⟩ := invariant_nums_covered2 p hp
    use q, hq₁
    simp [hq₂] at *;
    -- Since $j$ is at least $i_2$ and $q$ is less than $i_2$, the set operation on $j$ does not affect the value at $q$.
    have h_set_not_affect_q : j ≠ q := by
      grind;
    cases out_2 ; aesop

/-
PROVIDED SOLUTION
Same as goal_8: the setIfInBounds at index j >= i_2 doesn't affect indices q < i_2, so (out_2.setIfInBounds j 0)[q]! = out_2[q]! for q < i_2. Then use invariant_nums_covered2.
-/
theorem goal_8' (nums : Array ℤ) (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!) (i_1 : ℕ) (i_2 : ℕ) (out_1 : Array ℤ) (j : ℕ) (out_2 : Array ℤ) (invariant_j_lower2 : i_2 ≤ j) (invariant_j_upper2 : j ≤ out_2.size) (invariant_out_size2 : out_2.size = nums.size) (a : OfNat.ofNat 1 ≤ i_2) (a_1 : i_2 ≤ nums.size) (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!) (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_2[q]!) (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_2[p]! = nums[q]!) (invariant_k_le_out2 : i_2 ≤ out_2.size) (if_pos : j < out_2.size) (invariant_i_lower : OfNat.ofNat 1 ≤ i_1) (invariant_i_upper : i_1 ≤ nums.size) (invariant_k_lower : OfNat.ofNat 1 ≤ i_2) (invariant_k_upper : i_2 ≤ i_1) (invariant_out_size : out_1.size = nums.size) (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!) (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!) (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!) (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!) (if_neg : ¬nums = #[]) (done_1 : nums.size ≤ i_1) (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!) : ∀ p < nums.size, ∃ q < i_2, nums[p]! = (out_2.setIfInBounds j (OfNat.ofNat 0))[q]! := by
    intros p hp;
    obtain ⟨ q, hq₁, hq₂ ⟩ := invariant_nums_covered2 p hp;
    cases eq_or_ne q j <;> simp_all +decide [ Array.set ];
    · linarith;
    · grind

/-
PROVIDED SOLUTION
We need to show that for p < i_2, (out_2.setIfInBounds j 0)[p]! = nums[q]! for some q. Since j >= i_2 > p, the setIfInBounds at j doesn't affect index p, so (out_2.setIfInBounds j 0)[p]! = out_2[p]!. Then use invariant_prefix_from_nums2.
-/
theorem goal_9 (nums : Array ℤ) (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!) (i_1 : ℕ) (i_2 : ℕ) (out_1 : Array ℤ) (j : ℕ) (out_2 : Array ℤ) (invariant_j_lower2 : i_2 ≤ j) (invariant_j_upper2 : j ≤ out_2.size) (invariant_out_size2 : out_2.size = nums.size) (a : OfNat.ofNat 1 ≤ i_2) (a_1 : i_2 ≤ nums.size) (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!) (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_2[q]!) (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_2[p]! = nums[q]!) (invariant_k_le_out2 : i_2 ≤ out_2.size) (if_pos : j < out_2.size) (invariant_i_lower : OfNat.ofNat 1 ≤ i_1) (invariant_i_upper : i_1 ≤ nums.size) (invariant_k_lower : OfNat.ofNat 1 ≤ i_2) (invariant_k_upper : i_2 ≤ i_1) (invariant_out_size : out_1.size = nums.size) (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!) (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!) (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!) (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!) (if_neg : ¬nums = #[]) (done_1 : nums.size ≤ i_1) (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!) : ∀ p < i_2, ∃ q < nums.size, (out_2.setIfInBounds j (OfNat.ofNat 0))[p]! = nums[q]! := by
    intros p hp
    obtain ⟨q, hq_lt, hq_eq⟩ := invariant_prefix_from_nums2 p (by linarith);
    by_cases hj : j = p <;> simp_all +decide [ Array.getElem_set ];
    · linarith;
    · cases out_2 ; aesop

/-
PROVIDED SOLUTION
We need to show postcondition nums (i_2, out_3), which unfolds to four parts:
1. out_3.size = nums.size: from invariant_out_size2
2. PrefixStrictIncreasing out_3 i_2: from invariant_prefix_strict2
3. PrefixSameMembers nums i_2 out_3: We need k ≤ out.size (from invariant_k_le_out2) and the iff. The forward direction: x ∈ nums means some index p with nums[p] = x, use Array.getElem_mem or Array.mem_iff_getElem. Since done_1 gives nums.size ≤ i_1, invariant_nums_covered gives all p < i_1, but we have invariant_nums_covered2 which directly gives ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_3[q]!. The backward direction: invariant_prefix_from_nums2.
4. PrefixOccursInOrderFirst: construct the index map f using invariant_prefix_from_nums2. For each p < i_2, we get q < nums.size with out_3[p]! = nums[q]!. We need to pick the first occurrence. This is the hardest part; we can define f(p) = the minimum q such that nums[q] = out_3[p]. Since out_3 prefix is strictly increasing (invariant_prefix_strict2) and nums is sorted (require_1), the first occurrences must be in increasing order.

For the PrefixSameMembers part, use Array.mem_def or the fact that x ∈ a ↔ ∃ i, i < a.size ∧ a[i]! = x (or similar). The key hypotheses are invariant_nums_covered2 and invariant_prefix_from_nums2 which already express the membership relation in terms of indices.
-/
theorem goal_10 (nums : Array ℤ) (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!) (i_1 : ℕ) (i_2 : ℕ) (out_1 : Array ℤ) (a : OfNat.ofNat 1 ≤ i_2) (a_1 : i_2 ≤ nums.size) (i_4 : ℕ) (out_3 : Array ℤ) (invariant_i_lower : OfNat.ofNat 1 ≤ i_1) (invariant_i_upper : i_1 ≤ nums.size) (invariant_k_lower : OfNat.ofNat 1 ≤ i_2) (invariant_k_upper : i_2 ≤ i_1) (invariant_out_size : out_1.size = nums.size) (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!) (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!) (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!) (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!) (invariant_j_lower2 : i_2 ≤ i_4) (invariant_out_size2 : out_3.size = nums.size) (invariant_prefix_strict2 : i_2 ≤ out_3.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_3[i]! < out_3[i + OfNat.ofNat 1]!) (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_3[q]!) (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_3[p]! = nums[q]!) (invariant_k_le_out2 : i_2 ≤ out_3.size) (invariant_j_upper2 : i_4 ≤ out_3.size) (if_neg : ¬nums = #[]) (done_1 : nums.size ≤ i_1) (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!) (done_2 : out_3.size ≤ i_4) : postcondition nums (i_2, out_3) := by
    constructor <;> try linarith!;
    refine' ⟨ _, _, _ ⟩ <;> try tauto;
    · constructor;
      · linarith;
      · intro x; constructor <;> intro hx <;> simp_all +decide [ Array.mem_iff_getElem ] ;
        · obtain ⟨ p, hp, rfl ⟩ := hx; specialize invariant_nums_covered2 p hp; aesop;
        · obtain ⟨ i, hi, rfl ⟩ := hx; obtain ⟨ q, hq, hq' ⟩ := invariant_prefix_from_nums2 i hi; use q; aesop;
    · -- Define f(p) as the minimum q such that nums[q] = out_3[p]!.
      have h_f : ∀ p < i_2, ∃ q < nums.size, out_3[p]! = nums[q]! ∧ ∀ q' < q, nums[q']! ≠ out_3[p]! := by
        intro p hp; obtain ⟨ q, hq₁, hq₂ ⟩ := invariant_prefix_from_nums2 p hp; exact ⟨ Nat.find ( ⟨ q, hq₁, hq₂ ⟩ : ∃ q < nums.size, out_3[p]! = nums[q]! ), Nat.find_spec ( ⟨ q, hq₁, hq₂ ⟩ : ∃ q < nums.size, out_3[p]! = nums[q]! ) |>.1, Nat.find_spec ( ⟨ q, hq₁, hq₂ ⟩ : ∃ q < nums.size, out_3[p]! = nums[q]! ) |>.2, fun q' hq' => fun hq'' => Nat.find_min ( ⟨ q, hq₁, hq₂ ⟩ : ∃ q < nums.size, out_3[p]! = nums[q]! ) hq' ⟨ by linarith [ Nat.find_spec ( ⟨ q, hq₁, hq₂ ⟩ : ∃ q < nums.size, out_3[p]! = nums[q]! ) |>.1 ], by linarith [ Nat.find_spec ( ⟨ q, hq₁, hq₂ ⟩ : ∃ q < nums.size, out_3[p]! = nums[q]! ) |>.2 ] ⟩ ⟩ ;
      choose! f hf using h_f;
      refine' ⟨ f, _, _, _ ⟩;
      · exact fun p hp => ⟨ hf p hp |>.1, hf p hp |>.2.1 ⟩;
      · intros i j hij hj_lt_i2
        have h_out_lt : out_3[i]! < out_3[j]! := by
          have h_out_lt : ∀ i j, i < j → j < i_2 → out_3[i]! < out_3[j]! := by
            intros i j hij hj_lt_i2
            induction' hij with j hj ih;
            · exact invariant_prefix_strict2.2 i hj_lt_i2;
            · exact lt_trans ( ih ( Nat.lt_of_succ_lt hj_lt_i2 ) ) ( invariant_prefix_strict2.2 _ hj_lt_i2 );
          exact h_out_lt i j hij hj_lt_i2;
        contrapose! h_out_lt;
        -- Since $f j \leq f i$, we have $nums[f j]! \leq nums[f i]!$ by the sorted property of $nums$.
        have h_sorted : ∀ q1 q2, q1 ≤ q2 → q2 < nums.size → nums[q1]! ≤ nums[q2]! := by
          intro q1 q2 hq1q2 hq2_lt_size
          induction' hq1q2 with q1 q2 hq1q2 ih;
          · norm_num;
          · exact le_trans ( hq1q2 ( Nat.lt_of_succ_lt hq2_lt_size ) ) ( require_1 _ hq2_lt_size );
        linarith [ hf i ( by linarith ), hf j ( by linarith ), h_sorted ( f j ) ( f i ) h_out_lt ( by linarith [ hf i ( by linarith ), hf j ( by linarith ) ] ) ];
      · exact fun p hp q hq => hf p hp |>.2.2 q hq |> fun h => by simpa [ hf p hp |>.2.1 ] using h;

end Proof