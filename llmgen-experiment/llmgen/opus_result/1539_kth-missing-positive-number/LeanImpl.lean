import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

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
    3. A positive integer `m` is considered “missing” if `m ≥ 1` and `m` is not an element of `arr`.
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
def bsearch (arr : Array Nat) (k : Nat) (lo hi : Nat) : Nat :=
  if lo >= hi then lo
  else
    let mid := lo + (hi - lo) / 2
    let missing := arr[mid]! - (mid + 1)
    if missing < k then
      bsearch arr k (mid + 1) hi
    else
      bsearch arr k lo mid
termination_by hi - lo

def implementation (arr : Array Nat) (k : Nat) : Nat :=
  -- Binary search: find the smallest index where arr[index] - (index+1) >= k
  -- The answer is k + (number of array elements before that point)
  let n := arr.size
  let idx := bsearch arr k 0 n
  -- idx is the number of array elements that come before the answer
  k + idx
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
#assert_same_evaluation #[(implementation test1_arr test1_k), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr test2_k), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr test3_k), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr test4_k), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr test5_k), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr test6_k), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr test7_k), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr test8_k), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr test9_k), test9_Expected]
end Assertions

section Pbt
method implementationPbt (arr : Array Nat) (k : Nat)
  return (result : Nat)
  require precondition arr k
  ensures postcondition arr k result
  do
  return (implementation arr k)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
lemma bsearch_le_hi (arr : Array Nat) (k lo hi : Nat) (h : lo ≤ hi) : bsearch arr k lo hi ≤ hi := by
  suffices ∀ (n : Nat) (lo hi : Nat), lo ≤ hi → hi - lo < n → bsearch arr k lo hi ≤ hi from
    this (hi - lo + 1) lo hi h (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro lo hi _ h; omega
  | succ n ih =>
    intro lo hi hle hlt
    unfold bsearch
    split
    · omega
    · rename_i hge
      push_neg at hge
      have hmid_lt : lo + (hi - lo) / 2 < hi := by omega
      simp only []
      split
      · apply ih
        · omega
        · omega
      · have := ih lo (lo + (hi - lo) / 2) (by omega) (by omega)
        omega


theorem correctness_goal_0
    (arr : Array ℕ)
    (k : ℕ)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    : idx ≤ arr.size := by
    rw [hidx_def]
    exact bsearch_le_hi arr k 0 arr.size (Nat.zero_le _)

lemma arr_ge_index_plus_one (arr : Array ℕ) (hsi : strictlyIncreasing arr) (hap : allPositive arr) :
    ∀ i, i < arr.size → arr[i]! ≥ i + 1 := by
  intro i hi
  induction i with
  | zero => 
    have := hap 0 hi
    omega
  | succ n ih =>
    have hn_size : n < arr.size := by omega
    have := ih hn_size
    have hsi_step : arr[n]! < arr[n + 1]! := by
      apply hsi; omega
    omega

lemma strictly_increasing_missing_mono (arr : Array ℕ) (hsi : strictlyIncreasing arr) (hap : allPositive arr) :
    ∀ a b, a ≤ b → b < arr.size → arr[a]! + b ≤ arr[b]! + a := by
  intro a b hab hbs
  induction hab with
  | refl => omega
  | @step m hab' ih_step =>
    have hm_size : m < arr.size := by omega
    have ih := ih_step hm_size
    -- ih : arr[a]! + m ≤ arr[m]! + a
    have hsi_step : arr[m]! < arr[m + 1]! := by apply hsi; omega
    have h1 : arr[m.succ]! = arr[m + 1]! := rfl
    have h2 : (Nat.succ m : ℕ) = m + 1 := Nat.succ_eq_add_one m
    rw [h1, h2]
    omega


theorem correctness_goal_1_0
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    : ∀ (lo hi : ℕ),
  lo ≤ hi →
    hi ≤ arr.size →
      (∀ j < lo, j < arr.size → arr[j]! - (j + 1) < k) → ∀ j < bsearch arr k lo hi, j < arr.size → arr[j]! - (j + 1) < k := by
    suffices key : ∀ (n : ℕ) (lo hi : ℕ), hi - lo = n → lo ≤ hi → hi ≤ arr.size →
        (∀ j < lo, j < arr.size → arr[j]! - (j + 1) < k) → 
        ∀ j < bsearch arr k lo hi, j < arr.size → arr[j]! - (j + 1) < k by
      intro lo hi hle hhi hprev
      exact key (hi - lo) lo hi rfl hle hhi hprev
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro lo hi hn hle hhi hprev j hj hjs
      unfold bsearch at hj
      split at hj
      · exact hprev j hj hjs
      · rename_i h_not_ge
        push_neg at h_not_ge
        have hmid_lt_hi : lo + (hi - lo) / 2 < hi := by omega
        have hmid_lt_size : lo + (hi - lo) / 2 < arr.size := by omega
        -- Simplify let bindings in hj
        simp only at hj
        split at hj
        · rename_i hmissing
          have hdecr : hi - (lo + (hi - lo) / 2 + 1) < n := by omega
          have hprev' : ∀ j < lo + (hi - lo) / 2 + 1, j < arr.size → arr[j]! - (j + 1) < k := by
            intro i hi_bound hi_size
            by_cases hilo : i < lo
            · exact hprev i hilo hi_size
            · push_neg at hilo
              have hi_le_mid : i ≤ lo + (hi - lo) / 2 := by omega
              have hmono := strictly_increasing_missing_mono arr hsi hap i (lo + (hi - lo) / 2) hi_le_mid hmid_lt_size
              have hi_ge := arr_ge_index_plus_one arr hsi hap i hi_size
              have hmid_ge := arr_ge_index_plus_one arr hsi hap (lo + (hi - lo) / 2) hmid_lt_size
              omega
          exact ih (hi - (lo + (hi - lo) / 2 + 1)) hdecr (lo + (hi - lo) / 2 + 1) hi rfl (by omega) hhi hprev' j hj hjs
        · have hdecr : lo + (hi - lo) / 2 - lo < n := by omega
          exact ih (lo + (hi - lo) / 2 - lo) hdecr lo (lo + (hi - lo) / 2) rfl (by omega) (by omega) hprev j hj hjs

theorem correctness_goal_1
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    : ∀ j < idx, j < arr.size → arr[j]! - (j + 1) < k := by
    have hlemma : ∀ (lo hi : Nat), lo ≤ hi → hi ≤ arr.size →
        (∀ j, j < lo → j < arr.size → arr[j]! - (j + 1) < k) →
        (∀ j, j < bsearch arr k lo hi → j < arr.size → arr[j]! - (j + 1) < k) := by expose_names; exact (correctness_goal_1_0 arr k hk hsi hap idx hidx_def result hresult_def)
    intro j hj hjs
    rw [hidx_def] at hj
    exact hlemma 0 arr.size (Nat.zero_le _) (Nat.le_refl _) (fun j hj => absurd hj (Nat.not_lt_zero j)) j hj hjs

theorem correctness_goal_2_0
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    : ∀ (lo hi : ℕ),
  lo ≤ hi →
    hi ≤ arr.size →
      (∀ (j : ℕ), hi ≤ j → j < arr.size → arr[j]! - (j + 1) ≥ k) →
        ∀ (j : ℕ), bsearch arr k lo hi ≤ j → j < arr.size → arr[j]! - (j + 1) ≥ k := by
    intro lo hi
    induction h_eq : hi - lo using Nat.strongRecOn generalizing lo hi with
    | _ n ih =>
    -- ih : ∀ m < n, ∀ (lo hi : ℕ), hi - lo = m → lo ≤ hi → hi ≤ arr.size → ... → ...
    intro hlo_le_hi hhi_le hhi_inv j hj_ge hj_lt
    unfold bsearch at hj_ge
    by_cases hge : hi ≤ lo
    · -- base case: lo ≥ hi, bsearch = lo, so lo = hi
      simp [hge] at hj_ge
      have : lo = hi := by omega
      subst this
      exact hhi_inv j (by omega) hj_lt
    · -- inductive case: lo < hi
      push_neg at hge
      simp only [show ¬(hi ≤ lo) from by omega, ite_false] at hj_ge
      by_cases hmissing : arr[lo + (hi - lo) / 2]! - (lo + (hi - lo) / 2 + 1) < k
      · -- missing < k: recurse on (mid+1, hi)
        simp only [hmissing, ite_true] at hj_ge
        have hterm : hi - (lo + (hi - lo) / 2 + 1) < n := by omega
        exact ih _ hterm _ _ rfl (by omega) hhi_le hhi_inv j hj_ge hj_lt
      · -- missing ≥ k: recurse on (lo, mid)
        push_neg at hmissing
        simp only [show ¬(arr[lo + (hi - lo) / 2]! - (lo + (hi - lo) / 2 + 1) < k) from by omega, ite_false] at hj_ge
        set mid := lo + (hi - lo) / 2 with hmid_def
        have hmid_le : mid ≤ arr.size := by omega
        have new_inv : ∀ (j' : ℕ), mid ≤ j' → j' < arr.size → arr[j']! - (j' + 1) ≥ k := by
          intro j' hj'_ge hj'_lt
          by_cases hj'_ge_hi : hi ≤ j'
          · exact hhi_inv j' hj'_ge_hi hj'_lt
          · push_neg at hj'_ge_hi
            have hmid_lt_size : mid < arr.size := by omega
            have hmono := strictly_increasing_missing_mono arr hsi hap mid j' (by omega) hj'_lt
            have hge_mid := arr_ge_index_plus_one arr hsi hap mid hmid_lt_size
            have hge_j' := arr_ge_index_plus_one arr hsi hap j' hj'_lt
            omega
        have hterm : mid - lo < n := by omega
        exact ih _ hterm _ _ rfl (by omega) hmid_le new_inv j hj_ge hj_lt

theorem correctness_goal_2
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    : idx < arr.size → arr[idx]! - (idx + 1) ≥ k := by
    have h_upper : ∀ (lo hi : ℕ), lo ≤ hi → hi ≤ arr.size →
      (∀ j, hi ≤ j → j < arr.size → arr[j]! - (j + 1) ≥ k) →
      ∀ j, bsearch arr k lo hi ≤ j → j < arr.size → arr[j]! - (j + 1) ≥ k := by expose_names; exact (correctness_goal_2_0 arr k hk hsi hap idx hidx_def result hresult_def)
    intro hidx_lt
    have h_init : ∀ j, arr.size ≤ j → j < arr.size → arr[j]! - (j + 1) ≥ k := by
      intro j hj hjsz; omega
    have h_all := h_upper 0 arr.size (Nat.zero_le _) (Nat.le_refl _) h_init
    have h_idx_ge : bsearch arr k 0 arr.size ≤ idx := by omega
    exact h_all idx h_idx_ge hidx_lt

theorem correctness_goal_3
    (arr : Array ℕ)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    : ∀ i < arr.size, arr[i]! ≥ i + 1 := by
    intros; expose_names; exact arr_ge_index_plus_one arr hsi hap i h

theorem correctness_goal_4
    (arr : Array ℕ)
    (k : ℕ)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    (h_idx_le : idx ≤ arr.size)
    (h_bsearch_lo : ∀ j < idx, j < arr.size → arr[j]! - (j + 1) < k)
    (h_bsearch_hi : idx < arr.size → arr[idx]! - (idx + 1) ≥ k)
    (h_ge : ∀ i < arr.size, arr[i]! ≥ i + 1)
    : inArrayB arr result = false := by
    unfold inArrayB
    rw [Array.any_eq_false]
    intro i hi
    -- We have arr[i] (with proof hi), need to relate to arr[i]!
    have h_eq : arr[i]! = arr[i] := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp [beq_eq_false_iff_ne]
    -- Need to show arr[i] ≠ result
    by_cases h : i < idx
    · -- Case i < idx: arr[i]! < result
      have hlt := h_bsearch_lo i h hi
      have hge_i := h_ge i hi
      -- arr[i]! - (i+1) < k and arr[i]! ≥ i+1
      -- So arr[i]! < k + (i+1)
      -- Since i < idx, i+1 ≤ idx, so k + (i+1) ≤ k + idx = result
      -- Hence arr[i]! < result
      rw [← h_eq]
      omega
    · -- Case i ≥ idx: arr[i]! > result
      push_neg at h
      have hi_ge_idx : idx ≤ i := h
      have h_idx_lt : idx < arr.size := by omega
      have h_idx_ge_k := h_bsearch_hi h_idx_lt
      have hge_idx := h_ge idx h_idx_lt
      -- arr[idx]! ≥ k + (idx + 1)
      have h1 : arr[idx]! ≥ k + (idx + 1) := by omega
      -- From strictly_increasing_missing_mono: arr[idx]! + i ≤ arr[i]! + idx
      have hmono := strictly_increasing_missing_mono arr hsi hap idx i hi_ge_idx hi
      -- So arr[i]! ≥ arr[idx]! + i - idx ≥ k + idx + 1 + i - idx = k + i + 1
      have h2 : arr[i]! ≥ k + i + 1 := by omega
      -- result = k + idx and i ≥ idx, so k + i + 1 ≥ k + idx + 1 > result
      rw [← h_eq]
      omega

theorem correctness_goal_5_0
    (arr : Array ℕ)
    (k : ℕ)
    (hsi : strictlyIncreasing arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    (h_idx_le : idx ≤ arr.size)
    (h_bsearch_lo : ∀ j < idx, j < arr.size → arr[j]! - (j + 1) < k)
    (h_bsearch_hi : idx < arr.size → arr[idx]! - (idx + 1) ≥ k)
    (h_ge : ∀ i < arr.size, arr[i]! ≥ i + 1)
    (h_pos : 0 < result)
    : {m ∈ Finset.Icc 1 (result - 1) | inArrayB arr m = true}.card = idx := by
    set S := Finset.filter (fun m => inArrayB arr m = true) (Finset.Icc 1 (result - 1)) with hS_def
    
    -- Strict monotonicity
    have h_strict_mono : ∀ i j : ℕ, i < j → j < arr.size → arr[i]! < arr[j]! := by
      intro i j hij hj
      induction j with
      | zero => omega
      | succ n ih =>
        by_cases h : i = n
        · subst h; exact hsi i (by omega)
        · exact Nat.lt_trans (ih (by omega) (by omega)) (hsi n (by omega))
    
    -- getElem! when in bounds
    have h_getElem!_eq : ∀ j, (hj : j < arr.size) → arr[j]! = arr[j] := by
      intro j hj; simp [Array.getElem!_eq_getD, Array.getD, hj]

    -- Elements at index < idx are < result 
    have h_below_result : ∀ j, j < idx → arr[j]! < result := by
      intro j hj
      have hjs : j < arr.size := by omega
      have := h_bsearch_lo j hj hjs; have := h_ge j hjs; omega
    
    -- Elements at index ≥ idx are ≥ result
    have h_above_result : ∀ j, idx ≤ j → j < arr.size → arr[j]! ≥ result := by
      intro j hj hjs
      by_cases hidx_eq : idx = arr.size
      · omega
      · have hidx_lt : idx < arr.size := by omega
        have hhi := h_bsearch_hi hidx_lt
        have hge_idx := h_ge idx hidx_lt
        by_cases heq : j = idx
        · subst heq; omega
        · have := h_strict_mono idx j (by omega) hjs; omega

    -- inArrayB ↔ membership ↔ exists index
    have h_inArr_mem : ∀ m, inArrayB arr m = true ↔ m ∈ arr := by
      intro m
      simp [inArrayB, Array.any_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact Array.getElem_mem hi
      · intro hm; obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hm; exact ⟨i, hi, rfl⟩
    
    have h_mem_iff_idx : ∀ m, m ∈ arr ↔ ∃ j, j < arr.size ∧ arr[j]! = m := by
      intro m
      constructor
      · intro hm
        obtain ⟨j, hj, hjm⟩ := Array.mem_iff_getElem.mp hm
        exact ⟨j, hj, by rw [h_getElem!_eq j hj, hjm]⟩
      · intro ⟨j, hj, hjm⟩
        have : arr[j] = m := by rw [← h_getElem!_eq j hj]; exact hjm
        exact Array.mem_of_getElem this

    -- S = image of {0,...,idx-1} under arr[·]!
    set T := (Finset.range idx).image (fun j => arr[j]!) with hT_def
    
    have hST : S = T := by
      ext m
      constructor
      · intro hm
        simp only [hS_def, Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨hm1, hm2⟩, hm3⟩ := hm
        rw [h_inArr_mem, h_mem_iff_idx] at hm3
        obtain ⟨j, hjs, hjm⟩ := hm3
        simp only [hT_def, Finset.mem_image, Finset.mem_range]
        refine ⟨j, ?_, hjm⟩
        by_contra h
        push_neg at h
        have := h_above_result j h hjs
        omega
      · intro hm
        simp only [hT_def, Finset.mem_image, Finset.mem_range] at hm
        obtain ⟨j, hj, hjm⟩ := hm
        simp only [hS_def, Finset.mem_filter, Finset.mem_Icc]
        have hjs : j < arr.size := by omega
        constructor
        · constructor
          · have := h_ge j hjs; omega
          · have := h_below_result j hj; omega
        · rw [h_inArr_mem, h_mem_iff_idx]
          exact ⟨j, hjs, hjm⟩
    
    rw [hST]
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range idx
    · intro a ha b hb hab
      simp [Finset.mem_range] at ha hb
      have has : a < arr.size := by omega
      have hbs : b < arr.size := by omega
      by_contra h
      rcases Nat.lt_or_gt_of_ne h with h | h
      · exact absurd hab (Nat.ne_of_lt (h_strict_mono a b h hbs))
      · exact absurd hab (Nat.ne_of_gt (h_strict_mono b a h has))

theorem correctness_goal_5_1
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    (h_idx_le : idx ≤ arr.size)
    (h_bsearch_lo : ∀ j < idx, j < arr.size → arr[j]! - (j + 1) < k)
    (h_bsearch_hi : idx < arr.size → arr[idx]! - (idx + 1) ≥ k)
    (h_ge : ∀ i < arr.size, arr[i]! ≥ i + 1)
    (h_pos : 0 < result)
    (h_not_in : inArrayB arr result = false)
    (h_arr_in_range : {m ∈ Finset.Icc 1 (result - 1) | inArrayB arr m = true}.card = idx)
    : missingUpTo arr (result - 1) = result - 1 - {m ∈ Finset.Icc 1 (result - 1) | inArrayB arr m = true}.card := by
    sorry

theorem correctness_goal_5
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    (h_idx_le : idx ≤ arr.size)
    (h_bsearch_lo : ∀ j < idx, j < arr.size → arr[j]! - (j + 1) < k)
    (h_bsearch_hi : idx < arr.size → arr[idx]! - (idx + 1) ≥ k)
    (h_ge : ∀ i < arr.size, arr[i]! ≥ i + 1)
    (h_pos : 0 < result)
    (h_not_in : inArrayB arr result = false)
    : missingUpTo arr result.pred = k - 1 := by
    rw [Nat.pred_eq_sub_one]
    -- Now goal is: missingUpTo arr (result - 1) = k - 1
    -- Step 2: The number of arr elements in [1, result - 1] equals idx
    have h_arr_in_range : ((Finset.Icc 1 (result - 1)).filter (fun m => inArrayB arr m)).card = idx := by expose_names; exact (correctness_goal_5_0 arr k hsi idx hidx_def result hresult_def h_idx_le h_bsearch_lo h_bsearch_hi h_ge h_pos)
    -- Step 3: missingUpTo is total minus arr elements in range
    have h_missing_eq : missingUpTo arr (result - 1) = (result - 1) - ((Finset.Icc 1 (result - 1)).filter (fun m => inArrayB arr m)).card := by expose_names; exact (correctness_goal_5_1 arr k hk hsi hap idx hidx_def result hresult_def h_idx_le h_bsearch_lo h_bsearch_hi h_ge h_pos h_not_in h_arr_in_range)
    -- Now combine
    rw [h_missing_eq, h_arr_in_range]
    subst hresult_def; omega

theorem correctness_goal_6
    (arr : Array ℕ)
    (k : ℕ)
    (hk : k > 0)
    (hsi : strictlyIncreasing arr)
    (hap : allPositive arr)
    (idx : ℕ)
    (hidx_def : idx = bsearch arr k 0 arr.size)
    (result : ℕ)
    (hresult_def : result = k + idx)
    (h_idx_le : idx ≤ arr.size)
    (h_bsearch_lo : ∀ j < idx, j < arr.size → arr[j]! - (j + 1) < k)
    (h_bsearch_hi : idx < arr.size → arr[idx]! - (idx + 1) ≥ k)
    (h_ge : ∀ i < arr.size, arr[i]! ≥ i + 1)
    (h_pos : 0 < result)
    (h_not_in : inArrayB arr result = false)
    (h_missing_pred : missingUpTo arr result.pred = k - 1)
    : missingUpTo arr result = k := by
    sorry


theorem correctness_goal
    (arr : Array Nat)
    (k : Nat)
    (h_precond : precondition arr k)
    : postcondition arr k (implementation arr k) := by
    unfold precondition at h_precond
    obtain ⟨hk, hsi, hap⟩ := h_precond
    unfold implementation
    -- Let idx = bsearch arr k 0 arr.size
    set idx := bsearch arr k 0 arr.size with hidx_def
    set result := k + idx with hresult_def
    -- We need to show postcondition arr k result
    unfold postcondition
    -- We need: bsearch returns idx ≤ arr.size
    have h_idx_le : idx ≤ arr.size := by expose_names; exact (correctness_goal_0 arr k idx hidx_def)
    -- Key property of bsearch: for all j < idx, arr[j]! - (j+1) < k
    have h_bsearch_lo : ∀ j, j < idx → j < arr.size → arr[j]! - (j + 1) < k := by expose_names; exact (correctness_goal_1 arr k hk hsi hap idx hidx_def result hresult_def)
    -- Key property of bsearch: if idx < arr.size, then arr[idx]! - (idx+1) ≥ k
    have h_bsearch_hi : idx < arr.size → arr[idx]! - (idx + 1) ≥ k := by expose_names; exact (correctness_goal_2 arr k hk hsi hap idx hidx_def result hresult_def)
    -- For strictly increasing positive arrays, arr[i]! ≥ i + 1
    have h_ge : ∀ i, i < arr.size → arr[i]! ≥ i + 1 := by expose_names; exact (correctness_goal_3 arr hsi hap)
    -- result > 0
    have h_pos : 0 < result := by omega
    -- result is not in the array
    have h_not_in : inArrayB arr result = false := by expose_names; exact (correctness_goal_4 arr k hsi hap idx hidx_def result hresult_def h_idx_le h_bsearch_lo h_bsearch_hi h_ge)
    -- missingUpTo arr (Nat.pred result) = k - 1
    have h_missing_pred : missingUpTo arr (Nat.pred result) = k - 1 := by expose_names; exact (correctness_goal_5 arr k hk hsi hap idx hidx_def result hresult_def h_idx_le h_bsearch_lo h_bsearch_hi h_ge h_pos h_not_in)
    -- missingUpTo arr result = k
    have h_missing : missingUpTo arr result = k := by expose_names; exact (correctness_goal_6 arr k hk hsi hap idx hidx_def result hresult_def h_idx_le h_bsearch_lo h_bsearch_hi h_ge h_pos h_not_in h_missing_pred)
    exact ⟨h_pos, h_not_in, h_missing_pred, h_missing⟩
end Proof
