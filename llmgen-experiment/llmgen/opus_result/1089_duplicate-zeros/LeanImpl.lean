import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    1089. Duplicate Zeros: duplicate each occurrence of 0 in a fixed-length integer array, shifting right and truncating.
    Natural language breakdown:
    1. Input is an array of integers with a fixed length n.
    2. We define a conceptual output stream obtained by scanning the input left-to-right.
    3. Each nonzero input element contributes exactly one output element equal to itself.
    4. Each zero input element contributes exactly two consecutive output elements, both equal to 0.
    5. The actual returned array is the first n elements of this conceptual output stream (truncate to length n).
    6. Because the original problem updates in-place and returns nothing, we model the modified array as a returned array.
    7. Therefore the result must have the same size as the input.
    8. Every output index j (0 ≤ j < n) is produced by a unique input index i, determined by how many output elements are produced by prefixes of the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper: producedLen arr k = number of conceptual output elements produced by the first k input elements.
-- Each nonzero produces 1; each zero produces 2.
-- We use foldl over a prefix (arr.take k) to avoid recursion.
-- Note: we use Int = 0 propositionally; this is fine (not Float).
def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

-- Precondition: none.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the length-preserving truncation of duplicating zeros.
-- We characterize the mapping index-wise using the prefix produced lengths.
-- For each output index j, there is a unique input index i < n such that
-- producedLen arr i ≤ j < producedLen arr (i+1). The output value equals arr[i], but if arr[i]=0 then it is 0.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))
end Specs

section Impl
def implementation (arr : Array Int) : Array Int :=
  let n := arr.size
  -- Build the conceptual output stream (duplicating zeros), but stop once we have n elements
  let result := arr.foldl (fun (acc : Array Int) (x : Int) =>
    if acc.size >= n then acc
    else if x = 0 then
      let acc := acc.push 0
      if acc.size >= n then acc else acc.push 0
    else acc.push x
  ) #[]
  -- Truncate to exactly n elements (should already be at most n, but ensure correctness)
  result.take n
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,0,2,3,0,4,5,0]
-- Output: [1,0,0,2,3,0,0,4]
def test1_arr : Array Int := #[1, 0, 2, 3, 0, 4, 5, 0]
def test1_Expected : Array Int := #[1, 0, 0, 2, 3, 0, 0, 4]

-- Test case 2: Example 2 (no zeros)
def test2_arr : Array Int := #[1, 2, 3]
def test2_Expected : Array Int := #[1, 2, 3]

-- Test case 3: empty array
def test3_arr : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: single element zero
def test4_arr : Array Int := #[0]
def test4_Expected : Array Int := #[0]

-- Test case 5: single element nonzero
def test5_arr : Array Int := #[7]
def test5_Expected : Array Int := #[7]

-- Test case 6: all zeros (truncation preserves all zeros)
def test6_arr : Array Int := #[0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: zeros causing truncation of later elements
-- [1,0,0,2] -> conceptual: 1,0,0,0,0,2 -> take 4 => [1,0,0,0]
def test7_arr : Array Int := #[1, 0, 0, 2]
def test7_Expected : Array Int := #[1, 0, 0, 0]

-- Test case 8: negative values with zeros
-- [0,-1,0,2] -> conceptual: 0,0,-1,0,0,2 -> take 4 => [0,0,-1,0]
def test8_arr : Array Int := #[0, -1, 0, 2]
def test8_Expected : Array Int := #[0, 0, -1, 0]

-- Test case 9: trailing zero does not create a visible extra element after truncation
-- [1,2,0] -> conceptual: 1,2,0,0 -> take 3 => [1,2,0]
def test9_arr : Array Int := #[1, 2, 0]
def test9_Expected : Array Int := #[1, 2, 0]

-- Recommend to validate: boundary sizes (0/1), multiple zeros, truncation at end
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_arr), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr), test9_Expected]
end Assertions

section Pbt
method implementationPbt (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  return (implementation arr)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
private lemma producedLen_step (arr : Array ℤ) (i : Nat) (hi : i < arr.size) :
    producedLen arr (i + 1) = producedLen arr i + (if arr[i] = 0 then 2 else 1) := by
  simp only [producedLen]
  conv_lhs => rw [show arr.take (i + 1) = (arr.take i).push arr[i] from by
    apply Array.ext
    · simp
    · intro j h1 h2
      simp at h1 h2
      simp [Array.getElem_push]]
  rw [Array.foldl_push]
  split <;> omega


theorem correctness_goal_0_0
    (arr : Array ℤ)
    (n : ℕ)
    (hn : n = arr.size)
    (result_full : Array ℤ)
    (hrf : result_full =
  Array.foldl
    (fun acc x =>
      if acc.size ≥ n then acc
      else
        if x = 0 then
          let acc := acc.push 0;
          if acc.size ≥ n then acc else acc.push 0
        else acc.push x)
    #[] arr)
    (result : Array ℤ)
    (hr : result = result_full.take n)
    : n ≤
    (Array.foldl
        (fun acc x =>
          if acc.size ≥ n then acc
          else
            if x = 0 then
              let acc := acc.push 0;
              if acc.size ≥ n then acc else acc.push 0
            else acc.push x)
        #[] arr).size ∨
  (Array.foldl
        (fun acc x =>
          if acc.size ≥ n then acc
          else
            if x = 0 then
              let acc := acc.push 0;
              if acc.size ≥ n then acc else acc.push 0
            else acc.push x)
        #[] arr).size =
    producedLen arr n := by
    subst hn
    apply Array.foldl_induction
      (motive := fun k (acc : Array ℤ) => arr.size ≤ acc.size ∨ acc.size = producedLen arr k)
    · right; simp [producedLen]
    · intro ⟨i, hi⟩ acc ih
      show arr.size ≤ _ ∨ _ = producedLen arr (i + 1)
      change arr.size ≤ acc.size ∨ acc.size = producedLen arr i at ih
      have key := producedLen_step arr i hi
      rcases ih with h_left | h_right
      · -- n ≤ acc.size
        split
        · left; exact h_left
        · omega
      · -- acc.size = producedLen arr i
        split
        · -- outer guard true: acc.size ≥ arr.size
          left; omega
        · -- outer guard false: acc.size < arr.size
          rename_i hng
          push_neg at hng
          split
          · -- arr[⟨i,hi⟩] = 0
            rename_i hx
            have hxi : arr[i] = 0 := hx
            simp only [Array.size_push]
            split
            · -- inner guard true: acc.size + 1 ≥ arr.size
              left; simp [Array.size_push]; omega
            · -- inner guard false
              right
              simp [Array.size_push]
              rw [key, if_pos hxi]; omega
          · -- arr[⟨i,hi⟩] ≠ 0
            rename_i hx
            have hxi : ¬(arr[i] = 0) := hx
            right
            simp [Array.size_push]
            rw [key, if_neg hxi]; omega

theorem correctness_goal_0
    (arr : Array ℤ)
    (n : ℕ)
    (hn : n = arr.size)
    (result_full : Array ℤ)
    (hrf : result_full =
  Array.foldl
    (fun acc x =>
      if acc.size ≥ n then acc
      else
        if x = 0 then
          let acc := acc.push 0;
          if acc.size ≥ n then acc else acc.push 0
        else acc.push x)
    #[] arr)
    (result : Array ℤ)
    (hr : result = result_full.take n)
    : n ≤ result_full.size ∨ result_full.size = producedLen arr n := by
    have key : n ≤ (Array.foldl
      (fun (acc : Array ℤ) (x : ℤ) =>
        if acc.size ≥ n then acc
        else if x = 0 then
          let acc := acc.push 0
          if acc.size ≥ n then acc else acc.push 0
        else acc.push x)
      #[] arr).size ∨
      (Array.foldl
      (fun (acc : Array ℤ) (x : ℤ) =>
        if acc.size ≥ n then acc
        else if x = 0 then
          let acc := acc.push 0
          if acc.size ≥ n then acc else acc.push 0
        else acc.push x)
      #[] arr).size = producedLen arr n := by expose_names; exact (correctness_goal_0_0 arr n hn result_full hrf result hr)
    rw [hrf]
    exact key

theorem correctness_goal_1
    (arr : Array ℤ)
    (n : ℕ)
    (hn : n = arr.size)
    : producedLen arr n ≥ n := by
    have key : ∀ k : ℕ, k ≤ arr.size → producedLen arr k ≥ k := by
      intro k hk
      induction k with
      | zero => simp [producedLen]
      | succ k ih =>
        have hk' : k < arr.size := Nat.lt_of_succ_le hk
        rw [producedLen_step arr k hk']
        have ih' := ih (Nat.le_of_lt hk')
        split <;> omega
    have := key n (by omega)
    omega

theorem correctness_goal_2_0
    (arr : Array ℤ)
    (n : ℕ)
    (hn : n = arr.size)
    (result : Array ℤ)
    (h_result_size : result.size = n)
    : ∀ k < n, producedLen arr k < producedLen arr (k + 1) := by
    intro k hk
    have hk' : k < arr.size := by omega
    rw [producedLen_step arr k hk']
    split <;> omega

theorem correctness_goal_2_1
    (arr : Array ℤ)
    : producedLen arr 0 = 0 := by
    simp [producedLen, Array.take, Array.foldl]

theorem correctness_goal_2_2
    (arr : Array ℤ)
    (n : ℕ)
    (h_mono : ∀ k < n, producedLen arr k < producedLen arr (k + 1))
    : ∀ (a b : ℕ), a ≤ b → b ≤ n → producedLen arr a ≤ producedLen arr b := by
    intro a b hab hbn
    induction hab with
    | refl => exact Nat.le_refl _
    | @step m hle ih =>
      have hm_lt_n : m < n := Nat.lt_of_succ_le hbn
      have hm_le_n : m ≤ n := Nat.le_of_lt hm_lt_n
      have ih' := ih hm_le_n
      exact Nat.le_trans ih' (Nat.le_of_lt (h_mono m hm_lt_n))

theorem correctness_goal_2_3
    (arr : Array ℤ)
    (n : ℕ)
    (hn : n = arr.size)
    (result : Array ℤ)
    (h_producedLen_ge : producedLen arr n ≥ n)
    (h_result_size : result.size = n)
    (h_pl_zero : producedLen arr 0 = 0)
    : ∀ j < n, ∃ i < n, producedLen arr i ≤ j ∧ j < producedLen arr (i + 1) := by
    intro j hj
    have hj_lt_pln : j < producedLen arr n := by linarith
    -- Existence of k with j < producedLen arr (k+1)
    have hn_pos : 0 < n := by omega
    have hn_pred_succ : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
    have hexists : ∃ k, j < producedLen arr (k + 1) := by
      refine ⟨n - 1, ?_⟩
      rw [hn_pred_succ]
      exact hj_lt_pln
    let i := Nat.find hexists
    have hi_spec : j < producedLen arr (i + 1) := Nat.find_spec hexists
    have hi_min : ∀ m < i, ¬ (j < producedLen arr (m + 1)) := fun m hm => Nat.find_min hexists hm
    -- Show i < n
    have hi_lt_n : i < n := by
      have hle : i ≤ n - 1 := by
        apply Nat.find_min' hexists
        rw [hn_pred_succ]
        exact hj_lt_pln
      omega
    -- Show producedLen arr i ≤ j
    have hi_lower : producedLen arr i ≤ j := by
      cases hi2 : i with
      | zero =>
        have : producedLen arr 0 = 0 := h_pl_zero
        omega
      | succ k =>
        -- k < i = k + 1, so by minimality, ¬(j < producedLen arr (k + 1))
        have : i = k + 1 := hi2
        have hk_lt_i : k < i := by omega
        have := hi_min k hk_lt_i
        push_neg at this
        exact this
    exact ⟨i, hi_lt_n, hi_lower, hi_spec⟩

theorem correctness_goal_2_4
    (arr : Array ℤ)
    (n : ℕ)
    (h_pl_mono : ∀ (a b : ℕ), a ≤ b → b ≤ n → producedLen arr a ≤ producedLen arr b)
    : ∀ j < n,
  ∀ (i₁ i₂ : ℕ),
    i₁ < n →
      producedLen arr i₁ ≤ j →
        j < producedLen arr (i₁ + 1) → i₂ < n → producedLen arr i₂ ≤ j → j < producedLen arr (i₂ + 1) → i₁ = i₂ := by
    intro j hj i₁ i₂ hi₁ hpl₁_lo hpl₁_hi hi₂ hpl₂_lo hpl₂_hi
    by_contra h_ne
    rcases Nat.lt_or_gt_of_ne h_ne with h_lt | h_gt
    · -- i₁ < i₂
      have h_le : i₁ + 1 ≤ i₂ := h_lt
      have h_i₂_le_n : i₂ ≤ n := Nat.le_of_lt hi₂
      have h_mono_apply := h_pl_mono (i₁ + 1) i₂ h_le h_i₂_le_n
      omega
    · -- i₂ < i₁
      have h_le : i₂ + 1 ≤ i₁ := h_gt
      have h_i₁_le_n : i₁ ≤ n := Nat.le_of_lt hi₁
      have h_mono_apply := h_pl_mono (i₂ + 1) i₁ h_le h_i₁_le_n
      omega

-- Helper: for j < n and j < arr.size, (arr.take n)[j]! = arr[j]!
lemma take_getElem!_eq {arr : Array ℤ} {n j : ℕ} (hj_lt_n : j < n) (hj_lt_sz : j < arr.size) :
    (arr.take n)[j]! = arr[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  have hsz : j < (arr.take n).size := by
    rw [← Array.shrink_eq_take, Array.size_shrink]; omega
  rw [Array.getElem?_eq_getElem hsz]
  rw [Array.getElem?_eq_getElem hj_lt_sz]
  simp

-- Helper: push preserves getElem! at indices less than size
lemma push_getElem!_lt {arr : Array ℤ} {v : ℤ} {j : ℕ} (hj : j < arr.size) :
    (arr.push v)[j]! = arr[j]! := by
  rw [getElem!_pos (arr.push v) j (by simp [Array.size_push]; omega)]
  rw [getElem!_pos arr j hj]
  exact Array.getElem_push_lt hj

-- Helper: push getElem! at size equals the pushed value
lemma push_getElem!_eq {arr : Array ℤ} {v : ℤ} :
    (arr.push v)[arr.size]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_push]
  simp


theorem correctness_goal_2_5
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (n : ℕ)
    (hn : n = arr.size)
    (result_full : Array ℤ)
    (hrf : result_full =
  Array.foldl
    (fun acc x =>
      if acc.size ≥ n then acc
      else
        if x = 0 then
          let acc := acc.push 0;
          if acc.size ≥ n then acc else acc.push 0
        else acc.push x)
    #[] arr)
    (result : Array ℤ)
    (hr : result = result_full.take n)
    (h_size_bound : n ≤ result_full.size ∨ result_full.size = producedLen arr n)
    (h_producedLen_ge : producedLen arr n ≥ n)
    (h_result_size : result.size = n)
    (h_mono : ∀ k < n, producedLen arr k < producedLen arr (k + 1))
    (h_pl_zero : producedLen arr 0 = 0)
    (h_pl_mono : ∀ (a b : ℕ), a ≤ b → b ≤ n → producedLen arr a ≤ producedLen arr b)
    (h_exists : ∀ j < n, ∃ i < n, producedLen arr i ≤ j ∧ j < producedLen arr (i + 1))
    (h_unique : ∀ j < n,
  ∀ (i₁ i₂ : ℕ),
    i₁ < n →
      producedLen arr i₁ ≤ j →
        j < producedLen arr (i₁ + 1) → i₂ < n → producedLen arr i₂ ≤ j → j < producedLen arr (i₂ + 1) → i₁ = i₂)
    : ∀ j < n, ∀ i < n, producedLen arr i ≤ j → j < producedLen arr (i + 1) → result[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
    sorry

theorem correctness_goal_2
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (n : ℕ)
    (hn : n = arr.size)
    (result_full : Array ℤ)
    (hrf : result_full =
  Array.foldl
    (fun acc x =>
      if acc.size ≥ n then acc
      else
        if x = 0 then
          let acc := acc.push 0;
          if acc.size ≥ n then acc else acc.push 0
        else acc.push x)
    #[] arr)
    (result : Array ℤ)
    (hr : result = result_full.take n)
    (h_size_bound : n ≤ result_full.size ∨ result_full.size = producedLen arr n)
    (h_producedLen_ge : producedLen arr n ≥ n)
    (h_result_size : result.size = n)
    : ∀ j < n,
  ∃! i, i < n ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1) ∧ result[j]! = if arr[i]! = 0 then 0 else arr[i]! := by
    -- Key helper: producedLen is strictly increasing (increases by ≥ 1 each step)
    have h_mono : ∀ k, k < n → producedLen arr k < producedLen arr (k + 1) := by expose_names; exact (correctness_goal_2_0 arr n hn result h_result_size)
    -- producedLen 0 = 0
    have h_pl_zero : producedLen arr 0 = 0 := by expose_names; exact (correctness_goal_2_1 arr)
    -- producedLen is monotone: a ≤ b → producedLen arr a ≤ producedLen arr b (for a, b ≤ n)
    have h_pl_mono : ∀ a b, a ≤ b → b ≤ n → producedLen arr a ≤ producedLen arr b := by expose_names; exact (correctness_goal_2_2 arr n h_mono)
    -- Existence: for each j < n, there exists i < n with producedLen arr i ≤ j < producedLen arr (i+1)
    have h_exists : ∀ j, j < n → ∃ i, i < n ∧ producedLen arr i ≤ j ∧ j < producedLen arr (i + 1) := by expose_names; exact (correctness_goal_2_3 arr n hn result h_producedLen_ge h_result_size h_pl_zero)
    -- Uniqueness: if two indices satisfy the range condition, they are equal
    have h_unique : ∀ j, j < n → ∀ i₁ i₂, i₁ < n → producedLen arr i₁ ≤ j → j < producedLen arr (i₁ + 1) →
      i₂ < n → producedLen arr i₂ ≤ j → j < producedLen arr (i₂ + 1) → i₁ = i₂ := by expose_names; exact (correctness_goal_2_4 arr n h_pl_mono)
    -- Value correctness: the fold invariant ensures result values are correct
    have h_values : ∀ j, j < n → ∀ i, i < n → producedLen arr i ≤ j → j < producedLen arr (i + 1) →
      result[j]! = if arr[i]! = 0 then 0 else arr[i]! := by expose_names; exact (correctness_goal_2_5 arr h_precond n hn result_full hrf result hr h_size_bound h_producedLen_ge h_result_size h_mono h_pl_zero h_pl_mono h_exists h_unique)
    -- Combine everything
    intro j hj
    obtain ⟨i, hi_lt, hi_le, hi_gt⟩ := h_exists j hj
    have hval := h_values j hj i hi_lt hi_le hi_gt
    exact ExistsUnique.intro i ⟨hi_lt, hi_le, hi_gt, hval⟩ (fun y ⟨hy_lt, hy_le, hy_gt, _⟩ =>
      h_unique j hj y i hy_lt hy_le hy_gt hi_lt hi_le hi_gt)


theorem correctness_goal
    (arr : Array Int)
    (h_precond : precondition arr)
    : postcondition arr (implementation arr) := by
    unfold postcondition implementation
    -- We need to show two things about the result
    -- Let's define the result of the foldl
    set n := arr.size with hn
    set result_full := arr.foldl (fun (acc : Array Int) (x : Int) =>
      if acc.size >= n then acc
      else if x = 0 then
        let acc := acc.push 0
        if acc.size >= n then acc else acc.push 0
      else acc.push x) #[] with hrf
    set result := result_full.take n with hr
    -- Key invariant: after processing all elements, result_full has size ≥ n (if arr is nonempty) 
    -- and ≤ n+1, and the first min(producedLen arr k, n) elements match the output stream
    -- We'll establish that result_full.size ≥ n ∨ result_full.size = producedLen arr arr.size
    -- and that for j < min(result_full.size, n), result_full[j] matches the expected output
    
    -- Main invariant: after the fold, for all j < n that are in range,
    -- result_full[j] equals the expected output
    have h_size_bound : n ≤ result_full.size ∨ result_full.size = producedLen arr n := by expose_names; exact (correctness_goal_0 arr n hn result_full hrf result hr)
    have h_producedLen_ge : producedLen arr n ≥ n := by expose_names; exact (correctness_goal_1 arr n hn)
    have h_result_size : result.size = n := by expose_names; intros; expose_names; try simp_all; try grind
    have h_values : ∀ (j : Nat), j < n →
      ∃! (i : Nat),
        i < n ∧
        producedLen arr i ≤ j ∧
        j < producedLen arr (i + 1) ∧
        result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!) := by expose_names; exact (correctness_goal_2 arr h_precond n hn result_full hrf result hr h_size_bound h_producedLen_ge h_result_size)
    exact ⟨h_result_size, h_values⟩
end Proof
