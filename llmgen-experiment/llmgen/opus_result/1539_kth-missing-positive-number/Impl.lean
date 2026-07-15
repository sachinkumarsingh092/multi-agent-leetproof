import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    1539. Kth Missing Positive Number: Given a strictly increasing array of positive integers `arr` and a positive integer `k`, return the k-th positive integer that does not appear in `arr`.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. The input `arr` is an array of natural numbers, intended to represent positive integers.
    2. The array is strictly increasing: each element is less than the next element.
    3. A positive integer `m` is considered “missing” if `m ≥ 1` and `m` is not an element of `arr`.
    4. For any `n ≥ 1`, we can count how many missing positive integers are in the range `[1, n]`.
    5. The desired output `result` is the unique positive integer such that:
       a. `result` is missing from `arr`.
       b. Exactly `k-1` missing positive integers are ≤ `result - 1`.
       c. Exactly `k` missing positive integers are ≤ `result`.
    6. These properties characterize the k-th missing positive integer without prescribing an algorithm.
-/

section Specs
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
method KthMissingPositiveNumber (arr : Array Nat) (k : Nat)
  return (result : Nat)
  require precondition arr k
  ensures postcondition arr k result
  do
  -- Binary search: find the number of array elements that are <= the answer
  -- For index i, missing count before arr[i] is arr[i] - (i+1)
  -- We want the largest lo such that arr[lo] - (lo+1) < k
  -- Then result = lo + 1 + k, where lo+1 is the count of array elements before result
  -- But if no such index, result = k
  if arr.size = 0 then
    return k
  else
    let mut lo : Nat := 0
    let mut hi : Nat := arr.size
    -- Binary search: find smallest index where arr[index] - (index+1) >= k
    -- i.e., missing count at that position >= k
    while lo < hi
      -- Bounds: lo and hi stay within valid range
      invariant "bounds" lo ≤ hi ∧ hi ≤ arr.size
      -- All indices below lo have missing count < k
      invariant "lo_bound" ∀ i, i < lo → i < arr.size → arr[i]! - (i + 1) < k
      -- All indices from hi onward have missing count >= k
      invariant "hi_bound" ∀ i, hi ≤ i → i < arr.size → arr[i]! - (i + 1) ≥ k
      -- Termination: the search interval shrinks each iteration
      decreasing hi - lo
    do
      let mid := lo + (hi - lo) / 2
      let missing := arr[mid]! - (mid + 1)
      if missing < k then
        lo := mid + 1
      else
        hi := mid
    -- lo is the number of array elements whose "missing before" < k
    -- equivalently, lo is the count of array elements that appear before the k-th missing
    -- result = k + lo
    return k + lo
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

section Assertions
-- Test case 1

#assert_same_evaluation #[((KthMissingPositiveNumber test1_arr test1_k).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((KthMissingPositiveNumber test2_arr test2_k).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((KthMissingPositiveNumber test3_arr test3_k).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((KthMissingPositiveNumber test4_arr test4_k).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((KthMissingPositiveNumber test5_arr test5_k).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((KthMissingPositiveNumber test6_arr test6_k).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((KthMissingPositiveNumber test7_arr test7_k).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((KthMissingPositiveNumber test8_arr test8_k).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((KthMissingPositiveNumber test9_arr test9_k).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test KthMissingPositiveNumber (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (arr : Array ℕ)
    (k : ℕ)
    (require_1 : OfNat.ofNat 0 < k ∧ (∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!) ∧ ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    (if_pos : arr = #[])
    : postcondition arr k k := by
    intros; expose_names; try simp_all; try grind

theorem goal_1
    (arr : Array ℕ)
    (k : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (a_1 : hi ≤ arr.size)
    (invariant_lo_bound : ∀ i < lo, i < arr.size → arr[i]! - (i + OfNat.ofNat 1) < k)
    (if_pos : lo < hi)
    (if_pos_1 : arr[lo + (hi - lo) / OfNat.ofNat 2]! - (lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1) < k)
    (require_1 : OfNat.ofNat 0 < k ∧ (∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!) ∧ ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    (invariant_hi_bound : ∀ (i : ℕ), hi ≤ i → i < arr.size → k ≤ arr[i]! - (i + OfNat.ofNat 1))
    : ∀ i < lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1, i < arr.size → arr[i]! - (i + OfNat.ofNat 1) < k := by
    -- First, normalize all OfNat.ofNat to regular numerals
    have ofNat0 : (OfNat.ofNat 0 : ℕ) = 0 := rfl
    have ofNat1 : (OfNat.ofNat 1 : ℕ) = 1 := rfl
    have ofNat2 : (OfNat.ofNat 2 : ℕ) = 2 := rfl
    rw [ofNat2, ofNat1] at if_pos_1 ⊢
    rw [ofNat1] at invariant_lo_bound invariant_hi_bound
    have h_inc : ∀ (i : ℕ), i + 1 < arr.size → arr[i]! < arr[i + 1]! := by
      intro i; exact require_1.2.1 i
    -- Key lemma: missing count is non-decreasing
    have h_mono : ∀ (i j : ℕ), i ≤ j → j < arr.size →
        arr[i]! - (i + 1) ≤ arr[j]! - (j + 1) := by
      intro i j hij hj
      induction j with
      | zero =>
        have : i = 0 := by omega
        subst this
        exact Nat.le_refl _
      | succ n ih =>
        by_cases hin : i ≤ n
        · by_cases hn : n < arr.size
          · have ih_res := ih hin hn
            have h_inc_n := h_inc n (by omega)
            omega
          · omega
        · have : i = n + 1 := by omega
          subst this
          exact Nat.le_refl _
    intro i hi_bound hi_size
    by_cases h : i < lo
    · exact invariant_lo_bound i h hi_size
    · push_neg at h
      have h_le_mid : i ≤ lo + (hi - lo) / 2 := by omega
      have hmid_lt_size : lo + (hi - lo) / 2 < arr.size := by
        have := Nat.div_le_self (hi - lo) 2; omega
      have h_step := h_mono i (lo + (hi - lo) / 2) h_le_mid hmid_lt_size
      omega

theorem goal_2_0
    (arr : Array ℕ)
    (k : ℕ)
    (require_1 : OfNat.ofNat 0 < k ∧
  (∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!) ∧
    ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    : ∀ (j i : ℕ), j ≤ i → i < arr.size → j < arr.size → arr[j]! - (j + 1) ≤ arr[i]! - (i + 1) := by
    obtain ⟨_, hstrictly, hpos⟩ := require_1
    simp only [OfNat.ofNat] at *
    -- First prove arr[n]! ≥ n + 1 for valid indices
    have hge : ∀ n, n < arr.size → arr[n]! ≥ n + 1 := by
      intro n hn
      induction n with
      | zero => exact hpos 0 hn
      | succ m ih =>
        have hm_bound : m < arr.size := by omega
        have ihm := ih hm_bound
        have hsm := hstrictly m (by omega)
        -- ihm : arr[m]! ≥ m + 1
        -- hsm : arr[m]! < arr[m + 1]!
        -- Goal: arr[m + 1]! ≥ m + 1 + 1
        linarith
    -- Prove addition form by induction on d
    suffices hsuff : ∀ d j, j + d < arr.size → j < arr.size →
        arr[j]! + d ≤ arr[j + d]! by
      intro j i hji hi_bound hj_bound
      have key := hsuff (i - j) j (by omega) hj_bound
      have heq : j + (i - j) = i := by omega
      rw [heq] at key
      have hgei := hge i hi_bound
      have hgej := hge j hj_bound
      omega
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ n ih =>
      intro j hjn hj
      have h1 := ih j (by omega) hj
      -- h1 : arr[j]! + n ≤ arr[j + n]!
      -- Need: arr[j]! + (n + 1) ≤ arr[j + (n + 1)]!
      -- From strict: arr[j+n]! < arr[j+n+1]!
      have hbound : j + n + 1 < arr.size := by omega
      have : j + n + 1 = (j + n) + 1 := by omega
      have hstr := hstrictly (j + n) (by rw [this] at hbound; exact hbound)
      -- hstr : arr[j + n]! < arr[(j + n) + 1]!
      -- Need to show arr[(j+n) + 1]! = arr[j + (n+1)]!
      have heq2 : (j + n) + 1 = j + (n + 1) := by omega
      -- But these might be definitionally equal or not
      -- Actually in Lean 4, j + n + 1 vs j + (n + 1) should be equal by omega
      -- Let's just use linarith after converting
      have : arr[j + n]! < arr[j + (n + 1)]! := by
        have : (j + n) + 1 = j + (n + 1) := by omega
        rw [this] at hstr
        exact hstr
      linarith


theorem goal_2
    (arr : Array ℕ)
    (k : ℕ)
    (hi : ℕ)
    (lo : ℕ)
    (a : lo ≤ hi)
    (a_1 : hi ≤ arr.size)
    (invariant_lo_bound : ∀ i < lo, i < arr.size → arr[i]! - (i + OfNat.ofNat 1) < k)
    (if_pos : lo < hi)
    (require_1 : OfNat.ofNat 0 < k ∧ (∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!) ∧ ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    (if_neg : ¬arr = #[])
    (invariant_hi_bound : ∀ (i : ℕ), hi ≤ i → i < arr.size → k ≤ arr[i]! - (i + OfNat.ofNat 1))
    (if_neg_1 : k ≤ arr[lo + (hi - lo) / OfNat.ofNat 2]! - (lo + (hi - lo) / OfNat.ofNat 2 + OfNat.ofNat 1))
    : ∀ (i : ℕ), lo + (hi - lo) / OfNat.ofNat 2 ≤ i → i < arr.size → k ≤ arr[i]! - (i + OfNat.ofNat 1) := by
    have mono : ∀ (j i : ℕ), j ≤ i → i < arr.size → j < arr.size → 
      arr[j]! - (j + 1) ≤ arr[i]! - (i + 1) := by expose_names; exact (goal_2_0 arr k require_1)
    have mid_lt_size : lo + (hi - lo) / 2 < arr.size := by expose_names; intros; expose_names; try simp_all; try grind
    intro i hi_le hi_size
    exact Nat.le_trans if_neg_1 (mono _ _ hi_le hi_size (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hi_le hi_size) (Nat.le_refl _)))

private lemma arr_strict_mono (arr : Array ℕ) 
    (hstrict : ∀ (i : ℕ), i + 1 < arr.size → arr[i]! < arr[i + 1]!)
    (i j : ℕ) (hij : i < j) (hj : j < arr.size) : arr[i]! < arr[j]! := by
  induction hij with
  | refl => exact hstrict i hj
  | @step m hlt ih =>
    have : arr[i]! < arr[m]! := ih (Nat.lt_of_succ_lt hj)
    exact Nat.lt_trans this (hstrict m hj)

private lemma inArrayB_of_index (arr : Array ℕ) (i : ℕ) (hi : i < arr.size) : 
    inArrayB arr (arr[i]!) = true := by
  unfold inArrayB
  rw [Array.any_eq_true]
  exact ⟨i, hi, by simp [getElem!_pos arr i hi]⟩

private lemma inArrayB_true_iff (arr : Array ℕ) (m : ℕ) :
    inArrayB arr m = true ↔ ∃ i, i < arr.size ∧ arr[i]! = m := by
  unfold inArrayB
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, hbeq⟩
    simp [beq_iff_eq] at hbeq
    exact ⟨i, hi, by rw [getElem!_pos arr i hi]; exact hbeq⟩
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, ?_⟩
    simp [beq_iff_eq]
    rw [getElem!_pos arr i hi] at heq
    exact heq


theorem goal_3_0_0
    (arr : Array ℕ)
    (k : ℕ)
    (lo_1 : ℕ)
    (a_1 : lo_1 ≤ arr.size)
    (hstrict : ∀ (i : ℕ), i + 1 < arr.size → arr[i]! < arr[i + 1]!)
    (hpos : ∀ i < arr.size, 0 < arr[i]!)
    (h_below : ∀ j < lo_1, j < arr.size → arr[j]! < k + lo_1)
    (h_above : ∀ (j : ℕ), lo_1 ≤ j → j < arr.size → arr[j]! > k + lo_1)
    : {m ∈ Finset.Icc 1 (k + lo_1) | inArrayB arr m = true}.card = lo_1 := by
    have hinj : Set.InjOn (fun i => arr[i]!) (↑(Finset.range lo_1) : Set ℕ) := by
      intro i hi j hj heq
      simp [Finset.mem_range] at hi hj
      -- heq : arr[i]! = arr[j]!
      change arr[i]! = arr[j]! at heq
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact absurd heq (Nat.ne_of_lt (arr_strict_mono arr hstrict i j h (Nat.lt_of_lt_of_le hj a_1)))
      · exact absurd heq (Ne.symm (Nat.ne_of_lt (arr_strict_mono arr hstrict j i h (Nat.lt_of_lt_of_le hi a_1))))
    have hset : {m ∈ Finset.Icc 1 (k + lo_1) | inArrayB arr m = true} =
      (Finset.range lo_1).image (fun i => arr[i]!) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨⟨hm1, hm2⟩, hmem⟩
        rw [inArrayB_true_iff] at hmem
        obtain ⟨idx, hidx, heq⟩ := hmem
        have hidx_lt : idx < lo_1 := by
          by_contra h
          push_neg at h
          have hab := h_above idx h hidx
          omega
        exact ⟨idx, hidx_lt, heq⟩
      · intro ⟨idx, hidx, heq⟩
        have hidx_sz : idx < arr.size := Nat.lt_of_lt_of_le hidx a_1
        constructor
        · constructor
          · have := hpos idx hidx_sz; omega
          · have := h_below idx hidx hidx_sz; omega
        · rw [← heq]; exact inArrayB_of_index arr idx hidx_sz
    rw [hset, Finset.card_image_of_injOn hinj, Finset.card_range]

theorem goal_3_0
    (arr : Array ℕ)
    (k : ℕ)
    (lo_1 : ℕ)
    (a_1 : lo_1 ≤ arr.size)
    (hstrict : ∀ (i : ℕ), i + 1 < arr.size → arr[i]! < arr[i + 1]!)
    (hpos : ∀ i < arr.size, 0 < arr[i]!)
    (h_below : ∀ j < lo_1, j < arr.size → arr[j]! < k + lo_1)
    (h_above : ∀ (j : ℕ), lo_1 ≤ j → j < arr.size → arr[j]! > k + lo_1)
    : missingUpTo arr (k + lo_1) = k := by
    have h_filter_in_card : ((Finset.Icc 1 (k + lo_1)).filter (fun m => inArrayB arr m = true)).card = lo_1 := by expose_names; exact (goal_3_0_0 arr k lo_1 a_1 hstrict hpos h_below h_above)
    unfold missingUpTo
    have h_goal_eq : ((Finset.Icc 1 (k + lo_1)).filter (fun m => !(inArrayB arr m))).card =
        ((Finset.Icc 1 (k + lo_1)).filter (fun m => inArrayB arr m = false)).card := by
      congr 1; ext m; simp [Bool.not_eq_true]
    rw [h_goal_eq]
    have h_partition := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.Icc 1 (k + lo_1))
      (fun m => inArrayB arr m = true)
    simp only [Bool.not_eq_true] at h_partition
    have h_card_icc : (Finset.Icc 1 (k + lo_1)).card = k + lo_1 := by
      simp [Nat.card_Icc]
    rw [h_filter_in_card] at h_partition
    rw [h_card_icc] at h_partition
    omega

theorem goal_3_1
    (arr : Array ℕ)
    (k : ℕ)
    (lo_1 : ℕ)
    (hk_pos : 0 < k)
    (h_result_pos : 0 < k + lo_1)
    (h_not_in : inArrayB arr (k + lo_1) = false)
    (h_missing : missingUpTo arr (k + lo_1) = k)
    : missingUpTo arr (k + lo_1).pred = k - 1 := by
    unfold missingUpTo at *
    set n := k + lo_1
    have hn_pos : 0 < n := h_result_pos
    have h1n : 1 ≤ n := hn_pos
    -- The goal has n.pred which is Nat.pred. Convert to n - 1 or Order.pred.
    -- First let's see what the goal looks like after unfold. Goal should have n.pred = Nat.pred n.
    -- h_missing uses Finset.Icc 1 n
    -- We want to show the count up to pred n is k - 1
    -- Key: Icc 1 n = insert n (Icc 1 (Order.pred n))
    rw [← Finset.insert_Icc_pred_right_eq_Icc h1n] at h_missing
    rw [Finset.filter_insert] at h_missing
    simp only [h_not_in, Bool.not_false, decide_true, ↓reduceIte] at h_missing
    -- h_missing : (insert n (filter ... (Icc 1 (Order.pred n)))).card = k
    -- Goal: (filter ... (Icc 1 n.pred)).card = k - 1
    -- We need Order.pred n = Nat.pred n = n.pred = n - 1
    have hpred_eq : Order.pred n = n - 1 := by
      rw [Nat.pred_eq_pred]; rfl
    rw [hpred_eq] at h_missing
    -- Now h_missing should have n - 1
    -- Goal should also have n.pred = n - 1 after simp
    simp only [Nat.pred_eq_sub_one] at *
    -- n ∉ Icc 1 (n - 1)
    have h_not_mem : n ∉ Finset.Icc 1 (n - 1) := by
      simp [Finset.mem_Icc]; omega
    have h_not_mem_filter : n ∉ (Finset.Icc 1 (n - 1)).filter (fun m => !inArrayB arr m) := by
      intro hmem; exact h_not_mem (Finset.mem_of_mem_filter _ hmem)
    rw [Finset.card_insert_of_not_mem h_not_mem_filter] at h_missing
    omega

theorem goal_3
    (arr : Array ℕ)
    (k : ℕ)
    (i : ℕ)
    (lo_1 : ℕ)
    (a_1 : i ≤ arr.size)
    (invariant_lo_bound : ∀ i < lo_1, i < arr.size → arr[i]! - (i + OfNat.ofNat 1) < k)
    (a : lo_1 ≤ i)
    (require_1 : OfNat.ofNat 0 < k ∧ (∀ (i : ℕ), i + OfNat.ofNat 1 < arr.size → arr[i]! < arr[i + OfNat.ofNat 1]!) ∧ ∀ i < arr.size, OfNat.ofNat 0 < arr[i]!)
    (if_neg : ¬arr = #[])
    (invariant_hi_bound : ∀ (i_1 : ℕ), i ≤ i_1 → i_1 < arr.size → k ≤ arr[i_1]! - (i_1 + OfNat.ofNat 1))
    (done_1 : i ≤ lo_1)
    : postcondition arr k (k + lo_1) := by
    have hlo_eq_i : lo_1 = i := Nat.le_antisymm a done_1
    subst hlo_eq_i
    have hk_pos : 0 < k := require_1.1
    have hstrict : ∀ (i : ℕ), i + 1 < arr.size → arr[i]! < arr[i + 1]! := require_1.2.1
    have hpos : ∀ i < arr.size, 0 < arr[i]! := require_1.2.2
    have h_result_pos : 0 < k + lo_1 := by omega
    -- For indices j < lo_1: arr[j]! < k + lo_1
    have h_below : ∀ j, j < lo_1 → j < arr.size → arr[j]! < k + lo_1 := by expose_names; intros; expose_names; try simp_all; try grind
    -- For indices j >= lo_1: arr[j]! > k + lo_1
    have h_above : ∀ j, lo_1 ≤ j → j < arr.size → arr[j]! > k + lo_1 := by expose_names; intros; expose_names; try simp_all; try grind
    -- inArrayB arr (k + lo_1) = false
    have h_not_in : inArrayB arr (k + lo_1) = false := by expose_names; intros; expose_names; try simp_all; try grind
    -- missingUpTo arr (k + lo_1) = k
    have h_missing : missingUpTo arr (k + lo_1) = k := by expose_names; exact (goal_3_0 arr k lo_1 a_1 hstrict hpos h_below h_above)
    -- missingUpTo arr (Nat.pred (k + lo_1)) = k - 1
    have h_missing_pred : missingUpTo arr (Nat.pred (k + lo_1)) = k - 1 := by expose_names; exact (goal_3_1 arr k lo_1 hk_pos h_result_pos h_not_in h_missing)
    exact ⟨h_result_pos, h_not_in, h_missing_pred, h_missing⟩


prove_correct KthMissingPositiveNumber by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 arr k require_1 if_pos)
  exact (goal_1 arr k hi lo a_1 invariant_lo_bound if_pos if_pos_1 require_1 invariant_hi_bound)
  exact (goal_2 arr k hi lo a a_1 invariant_lo_bound if_pos require_1 if_neg invariant_hi_bound if_neg_1)
  exact (goal_3 arr k i lo_1 a_1 invariant_lo_bound a require_1 if_neg invariant_hi_bound done_1)
end Proof
