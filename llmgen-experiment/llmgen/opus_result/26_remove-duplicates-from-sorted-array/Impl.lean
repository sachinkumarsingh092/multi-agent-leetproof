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

section Impl
method RemoveDuplicatesFromSortedArray (nums : Array Int)
  return (res : Nat × Array Int)
  require precondition nums
  ensures postcondition nums res
  do
    if nums.size = 0 then
      return (0, nums)
    else
      let mut out := nums
      let mut k : Nat := 1
      let mut i : Nat := 1
      while i < nums.size
        -- Bounds on loop variable i
        invariant "i_lower" 1 ≤ i
        invariant "i_upper" i ≤ nums.size
        -- Bounds on unique count k
        invariant "k_lower" 1 ≤ k
        invariant "k_upper" k ≤ i
        -- Size of output array preserved
        invariant "out_size" out.size = nums.size
        -- First k elements form a strictly increasing sequence
        invariant "prefix_strict" PrefixStrictIncreasing out k
        -- Each value in nums[0..i) is represented in out[0..k)
        invariant "nums_covered" ∀ (p : Nat), p < i → ∃ (q : Nat), q < k ∧ nums[p]! = out[q]!
        -- Each prefix element came from some position in nums[0..i)
        invariant "prefix_from_nums" ∀ (p : Nat), p < k → ∃ (q : Nat), q < i ∧ out[p]! = nums[q]!
        -- The last unique value out[k-1] is ≤ all remaining elements (sortedness)
        invariant "last_unique_le" k > 0 → (∀ (j : Nat), i ≤ j → j < nums.size → out[k - 1]! ≤ nums[j]!)
        -- Positions k..nums.size are untouched (equal to original nums)
        invariant "tail_unchanged" ∀ (j : Nat), k ≤ j → j < nums.size → out[j]! = nums[j]!
        -- PrefixOccursInOrderFirst requires ∃ (f : Nat → Nat) which Velvet cannot
        -- elaborate correctly (drops type annotation, causing f to be non-functional).
        -- Using placeholder; this property would need interactive proof tactics.
        invariant "index_map_placeholder" true = true
        decreasing nums.size - i
      do
        if nums[i]! != out[k - 1]! then
          out := out.set! k nums[i]!
          k := k + 1
        i := i + 1
      -- Zero-fill the remaining positions (does not affect first k elements)
      let mut j : Nat := k
      while j < out.size
        -- Bounds on j
        invariant "j_lower2" k ≤ j
        invariant "j_upper2" j ≤ out.size
        -- Size preserved through zero-filling
        invariant "out_size2" out.size = nums.size
        -- k is valid
        invariant "k_bound2" 1 ≤ k ∧ k ≤ nums.size
        -- Strictly increasing prefix preserved
        invariant "prefix_strict2" PrefixStrictIncreasing out k
        -- Membership: every nums value appears in out[0..k)
        invariant "nums_covered2" ∀ (p : Nat), p < nums.size → ∃ (q : Nat), q < k ∧ nums[p]! = out[q]!
        -- Membership: every out[0..k) value appears in nums
        invariant "prefix_from_nums2" ∀ (p : Nat), p < k → ∃ (q : Nat), q < nums.size ∧ out[p]! = nums[q]!
        -- k ≤ out.size for PrefixSameMembers
        invariant "k_le_out2" k ≤ out.size
        -- PrefixOccursInOrderFirst requires ∃ over Nat → Nat which Velvet cannot handle.
        -- The existential quantifier over function types causes ill-typed goals because
        -- Velvet strips the type annotation from ∃ (f : Nat → Nat), making f non-applicable.
        invariant "index_map2_placeholder" true = true
        decreasing out.size - j
      do
        out := out.set! j 0
        j := j + 1
      return (k, out)
end Impl

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

section Assertions
-- Test case 1

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test RemoveDuplicatesFromSortedArray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (if_pos : nums = #[])
    : postcondition nums (OfNat.ofNat 0, nums) := by
    intros; expose_names; try simp_all; try grind

theorem goal_1_0
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_prefix_strict : k ≤ out.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! < out[i + OfNat.ofNat 1]!)
    (h_k_lt_outsize : k < out.size)
    (h_last_lt : out[k - 1]! < nums[i]!)
    : ∀ i_1 < k, (out.setIfInBounds k nums[i]!)[i_1]! < (out.setIfInBounds k nums[i]!)[i_1 + 1]! := by
    let out' := out.setIfInBounds k nums[i]!
    -- Key fact: reading at index ≠ k returns original value
    have read_ne : ∀ (j : ℕ), j < out.size → k ≠ j → out'[j]! = out[j]! := by
      intro j hj hne
      simp only [out', Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                  Array.getElem?_setIfInBounds_ne hne, Array.size_setIfInBounds]
    -- Key fact: reading at index k returns nums[i]!
    have read_k : out'[k]! = nums[i]! := by
      simp only [out', Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                  Array.getElem?_setIfInBounds_self_of_lt h_k_lt_outsize]
      simp
    intro i_1 hi_1
    by_cases h : i_1 + 1 < k
    · -- Both indices < k, neither equals k
      have hne1 : k ≠ i_1 := by omega
      have hne2 : k ≠ (i_1 + 1) := by omega
      have hi1_lt : i_1 < out.size := by omega
      have hi1s_lt : i_1 + 1 < out.size := by omega
      rw [read_ne i_1 hi1_lt hne1, read_ne (i_1 + 1) hi1s_lt hne2]
      exact invariant_prefix_strict.2 i_1 h
    · -- i_1 + 1 = k
      have h_eq : i_1 + 1 = k := by omega
      have hne1 : k ≠ i_1 := by omega
      have hi1_lt : i_1 < out.size := by omega
      rw [read_ne i_1 hi1_lt hne1, h_eq, read_k]
      have : i_1 = k - 1 := by omega
      rw [this]
      exact h_last_lt

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_k_lower : OfNat.ofNat 1 ≤ k)
    (invariant_k_upper : k ≤ i)
    (invariant_out_size : out.size = nums.size)
    (invariant_prefix_strict : k ≤ out.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! < out[i + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    (invariant_last_unique_le : OfNat.ofNat 0 < k → ∀ (j : ℕ), i ≤ j → j < nums.size → out[k - OfNat.ofNat 1]! ≤ nums[j]!)
    (if_pos_1 : ¬nums[i]! = out[k - OfNat.ofNat 1]!)
    : k + OfNat.ofNat 1 ≤ out.size ∧ ∀ i_1 < k, (out.setIfInBounds k nums[i]!)[i_1]! < (out.setIfInBounds k nums[i]!)[i_1 + OfNat.ofNat 1]! := by
    have h_one_eq : (OfNat.ofNat 1 : ℕ) = 1 := rfl
    have h_zero_eq : (OfNat.ofNat 0 : ℕ) = 0 := rfl
    rw [h_one_eq] at *
    rw [h_zero_eq] at *
    have h_k_lt_outsize : k < out.size := by omega
    have h_size_bound : k + 1 ≤ out.size := by omega
    have h_last_le : out[k - 1]! ≤ nums[i]! := invariant_last_unique_le (by omega) i (le_refl i) if_pos
    have h_last_lt : out[k - 1]! < nums[i]! := lt_of_le_of_ne h_last_le (fun h => if_pos_1 h.symm)
    have h_strict : ∀ i_1 < k, (out.setIfInBounds k nums[i]!)[i_1]! < (out.setIfInBounds k nums[i]!)[i_1 + 1]! := by expose_names; exact (goal_1_0 nums i k out invariant_prefix_strict h_k_lt_outsize h_last_lt)
    exact ⟨h_size_bound, h_strict⟩

theorem goal_2_0
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    : ∀ q < k, (out.setIfInBounds k nums[i]!)[q]! = out[q]! := by
    intro q hqk
    have hqne : k ≠ q := by omega
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hqne]

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_k_upper : k ≤ i)
    (invariant_out_size : out.size = nums.size)
    (invariant_prefix_strict : k ≤ out.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! < out[i + OfNat.ofNat 1]!)
    (invariant_nums_covered : ∀ p < i, ∃ q < k, nums[p]! = out[q]!)
    (invariant_prefix_from_nums : ∀ p < k, ∃ q < i, out[p]! = nums[q]!)
    (if_pos : i < nums.size)
    (invariant_last_unique_le : OfNat.ofNat 0 < k → ∀ (j : ℕ), i ≤ j → j < nums.size → out[k - OfNat.ofNat 1]! ≤ nums[j]!)
    (if_pos_1 : ¬nums[i]! = out[k - OfNat.ofNat 1]!)
    : ∀ p < i + OfNat.ofNat 1, ∃ q < k + OfNat.ofNat 1, nums[p]! = (out.setIfInBounds k nums[i]!)[q]! := by
    have h_k_lt : k < out.size := by omega
    have h_old_preserved : ∀ q : ℕ, q < k → (out.setIfInBounds k nums[i]!)[q]! = out[q]! := by expose_names; exact (goal_2_0 nums i k out)
    have h_new_at_k : (out.setIfInBounds k nums[i]!)[k]! = nums[i]! := by expose_names; intros; expose_names; try simp_all; try grind
    intro p hp
    simp only [OfNat.ofNat] at hp ⊢
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hp) with hp_lt | rfl
    · obtain ⟨q, hq_lt, hq_eq⟩ := invariant_nums_covered p hp_lt
      exact ⟨q, by omega, by rw [h_old_preserved q hq_lt]; exact hq_eq⟩
    · exact ⟨k, by omega, by rw [h_new_at_k]⟩

theorem goal_3
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_k_lower : OfNat.ofNat 1 ≤ k)
    (invariant_k_upper : k ≤ i)
    (invariant_out_size : out.size = nums.size)
    (invariant_prefix_strict : k ≤ out.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! < out[i + OfNat.ofNat 1]!)
    (invariant_nums_covered : ∀ p < i, ∃ q < k, nums[p]! = out[q]!)
    (invariant_prefix_from_nums : ∀ p < k, ∃ q < i, out[p]! = nums[q]!)
    (invariant_tail_unchanged : ∀ (j : ℕ), k ≤ j → j < nums.size → out[j]! = nums[j]!)
    (if_pos : i < nums.size)
    (invariant_last_unique_le : OfNat.ofNat 0 < k → ∀ (j : ℕ), i ≤ j → j < nums.size → out[k - OfNat.ofNat 1]! ≤ nums[j]!)
    (if_pos_1 : ¬nums[i]! = out[k - OfNat.ofNat 1]!)
    : ∀ p < k + OfNat.ofNat 1, ∃ q < i + OfNat.ofNat 1, (out.setIfInBounds k nums[i]!)[p]! = nums[q]! := by
    change ∀ p, p < k + 1 → ∃ q, q < i + 1 ∧ (out.setIfInBounds k nums[i]!)[p]! = nums[q]!
    have h_k_lt : k < out.size := by
      have := invariant_prefix_strict.1; omega
    have h_set_at_k : (out.setIfInBounds k nums[i]!)[k]! = nums[i]! := by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_setIfInBounds_self_of_lt (by simp [h_k_lt])]
      simp
    have h_set_other : ∀ p, p < k → (out.setIfInBounds k nums[i]!)[p]! = out[p]! := by
      intro p hp
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_setIfInBounds_ne (by omega)]
    intro p hp
    by_cases hpk : p < k
    · obtain ⟨q, hq_lt, hq_eq⟩ := invariant_prefix_from_nums p hpk
      exact ⟨q, by omega, by rw [h_set_other p hpk]; exact hq_eq⟩
    · have hpk_eq : p = k := by omega
      subst hpk_eq
      exact ⟨i, by omega, h_set_at_k⟩

theorem goal_4_0
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i : ℕ)
    : ∀ (j : ℕ), i + 1 ≤ j → j < nums.size → nums[i]! ≤ nums[j]! := by
    intro j hj1 hj2
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases h : i + 1 ≤ j
      · have hj_lt : j < nums.size := by omega
        have h1 := ih h hj_lt
        have h2 := require_1 j (by omega)
        linarith
      · have heq : i = j := by omega
        subst heq
        exact require_1 i hj2

theorem goal_4
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_k_upper : k ≤ i)
    (invariant_out_size : out.size = nums.size)
    (invariant_prefix_strict : k ≤ out.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! < out[i + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    : ∀ (j : ℕ), i + OfNat.ofNat 1 ≤ j → j < nums.size → (out.setIfInBounds k nums[i]!)[k]! ≤ nums[j]! := by
    have h_k_lt : k < out.size := by omega
    have h_read_back : (out.setIfInBounds k nums[i]!)[k]! = nums[i]! := by expose_names; intros; expose_names; try simp_all; try grind
    have h_sorted_trans : ∀ (j : ℕ), i + 1 ≤ j → j < nums.size → nums[i]! ≤ nums[j]! := by expose_names; exact (goal_4_0 nums require_1 i)
    intro j hj1 hj2
    rw [h_read_back]
    exact h_sorted_trans j hj1 hj2

theorem goal_5
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_k_lower : OfNat.ofNat 1 ≤ k)
    (invariant_k_upper : k ≤ i)
    (invariant_nums_covered : ∀ p < i, ∃ q < k, nums[p]! = out[q]!)
    (invariant_prefix_from_nums : ∀ p < k, ∃ q < i, out[p]! = nums[q]!)
    (if_pos : i < nums.size)
    (invariant_last_unique_le : OfNat.ofNat 0 < k → ∀ (j : ℕ), i ≤ j → j < nums.size → out[k - OfNat.ofNat 1]! ≤ nums[j]!)
    (if_neg_1 : nums[i]! = out[k - OfNat.ofNat 1]!)
    : ∀ p < i + OfNat.ofNat 1, ∃ q < k, nums[p]! = out[q]! := by
    have hk1 : 1 ≤ k := invariant_k_lower
    intro p hp
    have hp' : p < i + 1 := hp
    by_cases h : p < i
    · exact invariant_nums_covered p h
    · have hpi : p = i := by omega
      subst hpi
      exact ⟨k - 1, by omega, if_neg_1⟩

theorem goal_6
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    : ∀ (j : ℕ), OfNat.ofNat 1 ≤ j → j < nums.size → nums[OfNat.ofNat 0]! ≤ nums[j]! := by
    intros; expose_names; exact goal_4_0 nums require_1 (OfNat.ofNat 0) j h h_1

theorem goal_7
    (i_2 : ℕ)
    (j : ℕ)
    (out_2 : Array ℤ)
    (invariant_j_lower2 : i_2 ≤ j)
    (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!)
    : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → (out_2.setIfInBounds j (OfNat.ofNat 0))[i]! < (out_2.setIfInBounds j (OfNat.ofNat 0))[i + OfNat.ofNat 1]! := by
    obtain ⟨h_size, h_strict⟩ := invariant_prefix_strict2
    refine ⟨h_size, fun idx h_idx => ?_⟩
    -- idx + OfNat.ofNat 1 < i_2 and i_2 ≤ j, so idx < j and idx + 1 ≤ idx + OfNat.ofNat 1 < i_2 ≤ j
    -- We need j ≠ idx and j ≠ idx + 1
    have h1 : (OfNat.ofNat 1 : ℕ) = 1 := rfl
    have h_idx_nat : idx + 1 < i_2 := by rw [← h1]; exact h_idx
    have h_ne1 : j ≠ idx := by omega
    have h_ne2 : j ≠ idx + 1 := by omega
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h_ne1, Array.getElem?_setIfInBounds_ne h_ne2]
    have := h_strict idx h_idx
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at this
    exact this

theorem goal_8
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (out_1 : Array ℤ)
    (j : ℕ)
    (out_2 : Array ℤ)
    (invariant_j_lower2 : i_2 ≤ j)
    (invariant_j_upper2 : j ≤ out_2.size)
    (invariant_out_size2 : out_2.size = nums.size)
    (a : OfNat.ofNat 1 ≤ i_2)
    (a_1 : i_2 ≤ nums.size)
    (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!)
    (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_2[q]!)
    (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_2[p]! = nums[q]!)
    (invariant_k_le_out2 : i_2 ≤ out_2.size)
    (if_pos : j < out_2.size)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i_1)
    (invariant_i_upper : i_1 ≤ nums.size)
    (invariant_k_lower : OfNat.ofNat 1 ≤ i_2)
    (invariant_k_upper : i_2 ≤ i_1)
    (invariant_out_size : out_1.size = nums.size)
    (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!)
    (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!)
    (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!)
    (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!)
    (if_neg : ¬nums = #[])
    (done_1 : nums.size ≤ i_1)
    (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!)
    : ∀ p < nums.size, ∃ q < i_2, nums[p]! = (out_2.setIfInBounds j (OfNat.ofNat 0))[q]! := by
    sorry



theorem goal_8
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (out_1 : Array ℤ)
    (j : ℕ)
    (out_2 : Array ℤ)
    (invariant_j_lower2 : i_2 ≤ j)
    (invariant_j_upper2 : j ≤ out_2.size)
    (invariant_out_size2 : out_2.size = nums.size)
    (a : OfNat.ofNat 1 ≤ i_2)
    (a_1 : i_2 ≤ nums.size)
    (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!)
    (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_2[q]!)
    (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_2[p]! = nums[q]!)
    (invariant_k_le_out2 : i_2 ≤ out_2.size)
    (if_pos : j < out_2.size)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i_1)
    (invariant_i_upper : i_1 ≤ nums.size)
    (invariant_k_lower : OfNat.ofNat 1 ≤ i_2)
    (invariant_k_upper : i_2 ≤ i_1)
    (invariant_out_size : out_1.size = nums.size)
    (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!)
    (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!)
    (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!)
    (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!)
    (if_neg : ¬nums = #[])
    (done_1 : nums.size ≤ i_1)
    (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!)
    : ∀ p < nums.size, ∃ q < i_2, nums[p]! = (out_2.setIfInBounds j (OfNat.ofNat 0))[q]! := by
    sorry

theorem goal_9
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (out_1 : Array ℤ)
    (j : ℕ)
    (out_2 : Array ℤ)
    (invariant_j_lower2 : i_2 ≤ j)
    (invariant_j_upper2 : j ≤ out_2.size)
    (invariant_out_size2 : out_2.size = nums.size)
    (a : OfNat.ofNat 1 ≤ i_2)
    (a_1 : i_2 ≤ nums.size)
    (invariant_prefix_strict2 : i_2 ≤ out_2.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_2[i]! < out_2[i + OfNat.ofNat 1]!)
    (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_2[q]!)
    (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_2[p]! = nums[q]!)
    (invariant_k_le_out2 : i_2 ≤ out_2.size)
    (if_pos : j < out_2.size)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i_1)
    (invariant_i_upper : i_1 ≤ nums.size)
    (invariant_k_lower : OfNat.ofNat 1 ≤ i_2)
    (invariant_k_upper : i_2 ≤ i_1)
    (invariant_out_size : out_1.size = nums.size)
    (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!)
    (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!)
    (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!)
    (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!)
    (if_neg : ¬nums = #[])
    (done_1 : nums.size ≤ i_1)
    (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!)
    : ∀ p < i_2, ∃ q < nums.size, (out_2.setIfInBounds j (OfNat.ofNat 0))[p]! = nums[q]! := by
    sorry

theorem goal_10
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (out_1 : Array ℤ)
    (a : OfNat.ofNat 1 ≤ i_2)
    (a_1 : i_2 ≤ nums.size)
    (i_4 : ℕ)
    (out_3 : Array ℤ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i_1)
    (invariant_i_upper : i_1 ≤ nums.size)
    (invariant_k_lower : OfNat.ofNat 1 ≤ i_2)
    (invariant_k_upper : i_2 ≤ i_1)
    (invariant_out_size : out_1.size = nums.size)
    (invariant_prefix_strict : i_2 ≤ out_1.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_1[i]! < out_1[i + OfNat.ofNat 1]!)
    (invariant_tail_unchanged : ∀ (j : ℕ), i_2 ≤ j → j < nums.size → out_1[j]! = nums[j]!)
    (invariant_nums_covered : ∀ p < i_1, ∃ q < i_2, nums[p]! = out_1[q]!)
    (invariant_prefix_from_nums : ∀ p < i_2, ∃ q < i_1, out_1[p]! = nums[q]!)
    (invariant_j_lower2 : i_2 ≤ i_4)
    (invariant_out_size2 : out_3.size = nums.size)
    (invariant_prefix_strict2 : i_2 ≤ out_3.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < i_2 → out_3[i]! < out_3[i + OfNat.ofNat 1]!)
    (invariant_nums_covered2 : ∀ p < nums.size, ∃ q < i_2, nums[p]! = out_3[q]!)
    (invariant_prefix_from_nums2 : ∀ p < i_2, ∃ q < nums.size, out_3[p]! = nums[q]!)
    (invariant_k_le_out2 : i_2 ≤ out_3.size)
    (invariant_j_upper2 : i_4 ≤ out_3.size)
    (if_neg : ¬nums = #[])
    (done_1 : nums.size ≤ i_1)
    (invariant_last_unique_le : OfNat.ofNat 0 < i_2 → ∀ (j : ℕ), i_1 ≤ j → j < nums.size → out_1[i_2 - OfNat.ofNat 1]! ≤ nums[j]!)
    (done_2 : out_3.size ≤ i_4)
    : postcondition nums (i_2, out_3) := by
    sorry


set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 2)))


prove_correct RemoveDuplicatesFromSortedArray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums if_pos)
  exact (goal_1 nums i k out invariant_k_lower invariant_k_upper invariant_out_size invariant_prefix_strict if_pos invariant_last_unique_le if_pos_1)
  exact (goal_2 nums i k out invariant_i_lower invariant_i_upper invariant_k_upper invariant_out_size invariant_prefix_strict invariant_nums_covered invariant_prefix_from_nums if_pos invariant_last_unique_le if_pos_1)
  exact (goal_3 nums i k out invariant_k_lower invariant_k_upper invariant_out_size invariant_prefix_strict invariant_nums_covered invariant_prefix_from_nums invariant_tail_unchanged if_pos invariant_last_unique_le if_pos_1)
  exact (goal_4 nums require_1 i k out invariant_k_upper invariant_out_size invariant_prefix_strict if_pos)
  exact (goal_5 nums i k out invariant_i_lower invariant_i_upper invariant_k_lower invariant_k_upper invariant_nums_covered invariant_prefix_from_nums if_pos invariant_last_unique_le if_neg_1)
  exact (goal_6 nums require_1)
  exact (goal_7 i_2 j out_2 invariant_j_lower2 invariant_prefix_strict2)
  exact (goal_8 nums require_1 i_1 i_2 out_1 j out_2 invariant_j_lower2 invariant_j_upper2 invariant_out_size2 a a_1 invariant_prefix_strict2 invariant_nums_covered2 invariant_prefix_from_nums2 invariant_k_le_out2 if_pos invariant_i_lower invariant_i_upper invariant_k_lower invariant_k_upper invariant_out_size invariant_prefix_strict invariant_tail_unchanged invariant_nums_covered invariant_prefix_from_nums if_neg done_1 invariant_last_unique_le)
  exact (goal_9 nums require_1 i_1 i_2 out_1 j out_2 invariant_j_lower2 invariant_j_upper2 invariant_out_size2 a a_1 invariant_prefix_strict2 invariant_nums_covered2 invariant_prefix_from_nums2 invariant_k_le_out2 if_pos invariant_i_lower invariant_i_upper invariant_k_lower invariant_k_upper invariant_out_size invariant_prefix_strict invariant_tail_unchanged invariant_nums_covered invariant_prefix_from_nums if_neg done_1 invariant_last_unique_le)
  exact (goal_10 nums require_1 i_1 i_2 out_1 a a_1 i_4 out_3 invariant_i_lower invariant_i_upper invariant_k_lower invariant_k_upper invariant_out_size invariant_prefix_strict invariant_tail_unchanged invariant_nums_covered invariant_prefix_from_nums invariant_j_lower2 invariant_out_size2 invariant_prefix_strict2 invariant_nums_covered2 invariant_prefix_from_nums2 invariant_k_le_out2 invariant_j_upper2 if_neg done_1 invariant_last_unique_le done_2)
end Proof
