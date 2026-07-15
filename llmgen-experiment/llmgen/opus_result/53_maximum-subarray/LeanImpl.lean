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
    MaximumSubarray: return the maximum possible sum of a non-empty contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A contiguous subarray is determined by indices `start` and `stop` with `start < stop`.
    3. The sum of a subarray is the sum of the elements in `nums[start:stop]`.
    4. The result is the sum of some non-empty contiguous subarray (achievability).
    5. The result is greater than or equal to the sum of every non-empty contiguous subarray (maximality).
    6. The input must be non-empty so that at least one non-empty subarray exists.
-/

-- Sum of all elements in an array.
def arraySum (arr : Array Int) : Int :=
  arr.foldl (fun acc x => acc + x) 0

-- Sum of the contiguous segment nums[start:stop].
-- This uses Array.extract; the spec restricts start/stop so no clamping occurs.
def rangeSum (nums : Array Int) (start : Nat) (stop : Nat) : Int :=
  arraySum (nums.extract start stop)

-- Input must be non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- result is the maximum sum among all non-empty contiguous subarrays.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size ∧ rangeSum nums start stop = result) ∧
  (∀ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size → rangeSum nums start stop ≤ result)
end Specs

section Impl
def implementation (nums : Array Int) : Int :=
  -- Kadane's algorithm: O(n) time, O(1) space
  -- We use foldl with accumulator (currentEndingHere, maxSoFar)
  -- Initialize with the first element
  let first := nums[0]!
  let (_, globalMax) := nums.foldl (fun (acc : Int × Int) (x : Int) =>
    let (currentMax, globalMax) := acc
    let newCurrent := max x (currentMax + x)
    let newGlobal := max globalMax newCurrent
    (newCurrent, newGlobal)
  ) (first, first) 1
  globalMax
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [-2,1,-3,4,-1,2,1,-5,4] => 6 (subarray [4,-1,2,1])
def test1_nums : Array Int := #[-2, 1, -3, 4, -1, 2, 1, -5, 4]
def test1_Expected : Int := 6

-- Test case 2: Example 2 (single element)
def test2_nums : Array Int := #[1]
def test2_Expected : Int := 1

-- Test case 3: Example 3 (whole array is best)
def test3_nums : Array Int := #[5, 4, -1, 7, 8]
def test3_Expected : Int := 23

-- Test case 4: All negative (best is the least negative single element)
def test4_nums : Array Int := #[-8, -3, -6, -2, -5, -4]
def test4_Expected : Int := -2

-- Test case 5: Contains zeros; best is 0 (choose [0])
def test5_nums : Array Int := #[0, -1, 0, -2]
def test5_Expected : Int := 0

-- Test case 6: Mixed, best is a suffix/prefix segment
-- Best subarray is [3, -1, 2] with sum 4

def test6_nums : Array Int := #[-2, 3, -1, 2, -1]
def test6_Expected : Int := 4

-- Test case 7: Alternating small values
-- Best subarray is [1, -1, 1, -1, 1] has max 1 (any single 1)
def test7_nums : Array Int := #[1, -1, 1, -1, 1]
def test7_Expected : Int := 1

-- Test case 8: Best is the entire array

def test8_nums : Array Int := #[2, 3, 1]
def test8_Expected : Int := 6

-- Test case 9: Two elements, decreasing
-- Best is [10] not [10,-20]
def test9_nums : Array Int := #[10, -20]
def test9_Expected : Int := 10
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (nums : Array ℤ)
    : Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        (fun currentMax globalMax =>
            let newCurrent := max x (currentMax + x);
            let newGlobal := max globalMax newCurrent;
            (newCurrent, newGlobal))
          fst snd)
    (nums[0]!, nums[0]!) nums 1 =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        (fun currentMax globalMax =>
            let newCurrent := max x (currentMax + x);
            let newGlobal := max globalMax newCurrent;
            (newCurrent, newGlobal))
          fst snd)
    (nums[0]!, nums[0]!) (nums.extract 1) := by
    conv_lhs => rw [Array.foldl_eq_foldlM, Array.foldlM_start_stop]
    rfl

private lemma foldl_add_shift (arr : Array ℤ) (init : ℤ) :
    arr.foldl (fun acc x => acc + x) init = init + arr.foldl (fun acc x => acc + x) 0 := by
  have h := @Array.foldl_toList ℤ ℤ (fun acc x => acc + x) init arr
  rw [← h]
  have h2 := @Array.foldl_toList ℤ ℤ (fun acc x => acc + x) 0 arr
  rw [← h2]
  sorry

private lemma foldl_add_shift' (l : List ℤ) (init : ℤ) :
    l.foldl (fun acc x => acc + x) init = init + l.foldl (fun acc x => acc + x) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (init + h)]
    conv_rhs => rw [ih (0 + h)]
    ring

private lemma foldl_add_shift_arr (arr : Array ℤ) (init : ℤ) :
    arr.foldl (fun acc x => acc + x) init = init + arr.foldl (fun acc x => acc + x) 0 := by
  rw [← Array.foldl_toList (f := fun acc x => acc + x) (init := init) (xs := arr)]
  rw [← Array.foldl_toList (f := fun acc x => acc + x) (init := 0) (xs := arr)]
  exact foldl_add_shift' arr.toList init

private lemma arraySum_append (a b : Array ℤ) : arraySum (a ++ b) = arraySum a + arraySum b := by
  simp [arraySum, Array.foldl_append]
  rw [foldl_add_shift_arr]

private lemma arraySum_singleton (x : ℤ) : arraySum #[x] = x := by
  simp [arraySum, Array.foldl]

private lemma extract_single (nums : Array ℤ) (t : ℕ) (ht : t < nums.size) :
    nums.extract t (t + 1) = #[nums[t]] := by
  apply Array.ext
  · simp [Array.size_extract]; omega
  · intro i h1 h2
    simp [Array.size_extract] at h1
    have : i = 0 := by omega
    subst this
    simp [Array.getElem_extract]

private lemma rangeSum_split (nums : Array ℤ) (s t : ℕ) (hst : s ≤ t) (ht : t < nums.size) :
    rangeSum nums s (t + 1) = rangeSum nums s t + nums[t] := by
  simp [rangeSum]
  have h1 : nums.extract s (t + 1) = nums.extract s t ++ nums.extract t (t + 1) := by
    rw [Array.extract_append_extract]
    congr 1 <;> omega
  rw [h1, arraySum_append, extract_single nums t ht, arraySum_singleton]

private lemma rangeSum_single (nums : Array ℤ) (t : ℕ) (ht : t < nums.size) :
    rangeSum nums t (t + 1) = nums[t] := by
  simp [rangeSum, extract_single nums t ht, arraySum_singleton]

private lemma rangeSum_empty (nums : Array ℤ) (s : ℕ) :
    rangeSum nums s s = 0 := by
  simp [rangeSum, arraySum, Array.extract_empty_of_stop_le_start (le_refl s)]

private lemma kadane_invariant_step
    (nums : Array ℤ) (i : ℕ) (curMax globMax : ℤ)
    (hi_bound : i + 1 < nums.size)
    (h1 : ∃ s, s ≤ i ∧ rangeSum nums s (i + 1) = curMax)
    (h2 : ∀ s, s ≤ i → rangeSum nums s (i + 1) ≤ curMax)
    (h3 : ∃ s t, s < t ∧ t ≤ i + 1 ∧ t ≤ nums.size ∧ rangeSum nums s t = globMax)
    (h4 : ∀ s t, s < t → t ≤ i + 1 → rangeSum nums s t ≤ globMax)
    (h5 : i + 1 ≤ nums.size) :
    let nc := max nums[i + 1] (curMax + nums[i + 1])
    let ng := max globMax nc
    (∃ s, s ≤ i + 1 ∧ rangeSum nums s (i + 2) = nc) ∧
    (∀ s, s ≤ i + 1 → rangeSum nums s (i + 2) ≤ nc) ∧
    (∃ s t, s < t ∧ t ≤ i + 2 ∧ t ≤ nums.size ∧ rangeSum nums s t = ng) ∧
    (∀ s t, s < t → t ≤ i + 2 → rangeSum nums s t ≤ ng) ∧
    (i + 2 ≤ nums.size) := by
  intro nc ng
  obtain ⟨s₀, hs₀le, hs₀eq⟩ := h1
  have h_i2 : i + 2 = (i + 1) + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · -- (1) Achievability for nc
    by_cases hcase : curMax + nums[i + 1] ≤ nums[i + 1]
    · refine ⟨i + 1, le_refl _, ?_⟩
      rw [h_i2, rangeSum_single nums (i+1) hi_bound]
      exact (max_eq_left hcase).symm
    · push_neg at hcase
      refine ⟨s₀, by omega, ?_⟩
      rw [h_i2, rangeSum_split nums s₀ (i+1) (by omega) hi_bound, hs₀eq]
      exact (max_eq_right (le_of_lt hcase)).symm
  · -- (2) Maximality for nc
    intro s hs
    by_cases hcase : s = i + 1
    · subst hcase
      rw [h_i2, rangeSum_single nums (i+1) hi_bound]
      exact le_max_left _ _
    · have hsi : s ≤ i := by omega
      rw [h_i2, rangeSum_split nums s (i+1) (by omega) hi_bound]
      calc rangeSum nums s (i + 1) + nums[i + 1]
          ≤ curMax + nums[i + 1] := by linarith [h2 s hsi]
        _ ≤ nc := le_max_right _ _
  · -- (3) Achievability for ng
    by_cases hcase : nc ≤ globMax
    · obtain ⟨s₁, t₁, hst, htb, htb2, heq⟩ := h3
      exact ⟨s₁, t₁, hst, by omega, htb2, by rw [show ng = globMax from max_eq_left hcase]; exact heq⟩
    · push_neg at hcase
      have hng_eq : ng = nc := max_eq_right (le_of_lt hcase)
      by_cases hcase2 : curMax + nums[i + 1] ≤ nums[i + 1]
      · exact ⟨i+1, i+2, by omega, by omega, by omega,
          by rw [hng_eq, h_i2, rangeSum_single nums (i+1) hi_bound]; exact (max_eq_left hcase2).symm⟩
      · push_neg at hcase2
        exact ⟨s₀, i+2, by omega, by omega, by omega,
          by rw [hng_eq, h_i2, rangeSum_split nums s₀ (i+1) (by omega) hi_bound, hs₀eq]; exact (max_eq_right (le_of_lt hcase2)).symm⟩
  · -- (4) Maximality for ng
    intro s t hst htb
    by_cases ht : t ≤ i + 1
    · exact le_trans (h4 s t hst ht) (le_max_left _ _)
    · have : t = i + 2 := by omega
      subst this
      suffices h : rangeSum nums s (i + 2) ≤ nc from le_trans h (le_max_right _ _)
      by_cases hcase : s = i + 1
      · subst hcase
        rw [h_i2, rangeSum_single nums (i+1) hi_bound]
        exact le_max_left _ _
      · have hsi : s ≤ i := by omega
        rw [h_i2, rangeSum_split nums s (i+1) (by omega) hi_bound]
        calc rangeSum nums s (i + 1) + nums[i + 1]
            ≤ curMax + nums[i + 1] := by linarith [h2 s hsi]
          _ ≤ nc := le_max_right _ _


theorem correctness_goal_0_1
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h_sz : nums.size > 0)
    (h_fold_eq : Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        (fun currentMax globalMax =>
            let newCurrent := max x (currentMax + x);
            let newGlobal := max globalMax newCurrent;
            (newCurrent, newGlobal))
          fst snd)
    (nums[0]!, nums[0]!) nums 1 =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        (fun currentMax globalMax =>
            let newCurrent := max x (currentMax + x);
            let newGlobal := max globalMax newCurrent;
            (newCurrent, newGlobal))
          fst snd)
    (nums[0]!, nums[0]!) (nums.extract 1))
    : (∃ start stop,
    start < stop ∧
      stop ≤ nums.size ∧
        rangeSum nums start stop =
          (Array.foldl
              (fun acc x =>
                Prod.casesOn acc fun fst snd =>
                  (fun currentMax globalMax =>
                      let newCurrent := max x (currentMax + x);
                      let newGlobal := max globalMax newCurrent;
                      (newCurrent, newGlobal))
                    fst snd)
              (nums[0]!, nums[0]!) nums 1).2) ∧
  ∀ (start stop : ℕ),
    start < stop ∧ stop ≤ nums.size →
      rangeSum nums start stop ≤
        (Array.foldl
            (fun acc x =>
              Prod.casesOn acc fun fst snd =>
                (fun currentMax globalMax =>
                    let newCurrent := max x (currentMax + x);
                    let newGlobal := max globalMax newCurrent;
                    (newCurrent, newGlobal))
                  fst snd)
            (nums[0]!, nums[0]!) nums 1).2 := by
    sorry

theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (f : ℤ × ℤ → ℤ → ℤ × ℤ)
    (hf_def : f = fun acc x =>
  Prod.casesOn acc fun fst snd =>
    (fun currentMax globalMax =>
        let newCurrent := max x (currentMax + x);
        let newGlobal := max globalMax newCurrent;
        (newCurrent, newGlobal))
      fst snd)
    (first : ℤ)
    (hfirst_def : first = nums[0]!)
    (pair : ℤ × ℤ)
    (hpair_def : pair = Array.foldl f (first, first) nums 1)
    : (∃ start stop, start < stop ∧ stop ≤ nums.size ∧ rangeSum nums start stop = pair.2) ∧
  ∀ (start stop : ℕ), start < stop ∧ stop ≤ nums.size → rangeSum nums start stop ≤ pair.2 := by
    have h_sz : nums.size > 0 := h_precond
    subst hf_def hfirst_def hpair_def
    -- Now pair.2 = (Array.foldl (fun acc x => ...) (nums[0]!, nums[0]!) nums 1).2
    -- We need to establish the invariant via foldl_induction
    -- First rewrite the fold to be over the extracted array
    have h_fold_eq : Array.foldl (fun (acc : ℤ × ℤ) (x : ℤ) =>
        let (currentMax, globalMax) := acc
        let newCurrent := max x (currentMax + x)
        let newGlobal := max globalMax newCurrent
        (newCurrent, newGlobal)) (nums[0]!, nums[0]!) nums 1 =
      (nums.extract 1 nums.size).foldl (fun (acc : ℤ × ℤ) (x : ℤ) =>
        let (currentMax, globalMax) := acc
        let newCurrent := max x (currentMax + x)
        let newGlobal := max globalMax newCurrent
        (newCurrent, newGlobal)) (nums[0]!, nums[0]!) := by
      expose_names; exact (correctness_goal_0_0 nums)
    -- The main invariant proved by foldl_induction
    have h_main : (∃ start stop, start < stop ∧ stop ≤ nums.size ∧
        rangeSum nums start stop = (Array.foldl (fun (acc : ℤ × ℤ) (x : ℤ) =>
          let (currentMax, globalMax) := acc
          let newCurrent := max x (currentMax + x)
          let newGlobal := max globalMax newCurrent
          (newCurrent, newGlobal)) (nums[0]!, nums[0]!) nums 1).2) ∧
      ∀ (start stop : ℕ), start < stop ∧ stop ≤ nums.size →
        rangeSum nums start stop ≤ (Array.foldl (fun (acc : ℤ × ℤ) (x : ℤ) =>
          let (currentMax, globalMax) := acc
          let newCurrent := max x (currentMax + x)
          let newGlobal := max globalMax newCurrent
          (newCurrent, newGlobal)) (nums[0]!, nums[0]!) nums 1).2 := by
      expose_names; exact (correctness_goal_0_1 nums h_precond h_sz h_fold_eq)
    exact h_main


theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
    unfold postcondition implementation
    -- Let's define the result value
    set f := (fun (acc : Int × Int) (x : Int) =>
      let (currentMax, globalMax) := acc
      let newCurrent := max x (currentMax + x)
      let newGlobal := max globalMax newCurrent
      (newCurrent, newGlobal)) with hf_def
    set first := nums[0]! with hfirst_def
    set pair := nums.foldl f (first, first) 1 with hpair_def
    simp only []
    -- The main invariant: after Kadane's fold, the second component satisfies postcondition
    have h_main : (∃ (start : Nat) (stop : Nat),
        start < stop ∧ stop ≤ nums.size ∧ rangeSum nums start stop = pair.2) ∧
      (∀ (start : Nat) (stop : Nat),
        start < stop ∧ stop ≤ nums.size → rangeSum nums start stop ≤ pair.2) := by expose_names; exact (correctness_goal_0 nums h_precond f hf_def first hfirst_def pair hpair_def)
    exact h_main
end Proof
