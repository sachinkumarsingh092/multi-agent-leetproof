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

section Specs
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
method MaximumSubarray (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Kadane's algorithm: O(n) time, O(1) space
  let mut currentMax := nums[0]!
  let mut globalMax := nums[0]!
  let mut i := 1
  while i < nums.size
    -- Bound on loop variable (lower)
    -- Init: i=1, so 1≤1. Pres: i increments but loop guard ensures i<nums.size before increment. Suff: with ¬(i<nums.size), gives i=nums.size.
    invariant "i_lower" 1 ≤ i
    -- Bound on loop variable (upper)
    invariant "i_upper" i ≤ nums.size
    -- currentMax equals some valid subarray sum ending at index i
    -- Init: start=0, rangeSum nums 0 1 = nums[0]! = currentMax.
    -- Pres: if currentMax+val > val, extend the witness; else start fresh at i.
    invariant "cm_witness" ∃ (start : Nat), start < i ∧ rangeSum nums start i = currentMax
    -- currentMax is the maximum subarray sum ending at index i
    -- Init: only start=0 possible, rangeSum nums 0 1 = currentMax.
    -- Pres: max(currentMax+val, val) ≥ rangeSum nums start (i+1) for all start < i+1.
    invariant "cm_max" ∀ (start : Nat), start < i → rangeSum nums start i ≤ currentMax
    -- globalMax equals some valid subarray sum within nums[0..i]
    -- Init: start=0, stop=1.
    -- Pres: globalMax is updated to max(globalMax, currentMax), preserving witness.
    invariant "gm_witness" ∃ (start stop : Nat), start < stop ∧ stop ≤ i ∧ rangeSum nums start stop = globalMax
    -- globalMax is the maximum subarray sum within nums[0..i]
    -- Init: only subarray is nums[0..1]. Suff: at i=nums.size, this is the full postcondition.
    invariant "gm_max" ∀ (start stop : Nat), start < stop ∧ stop ≤ i → rangeSum nums start stop ≤ globalMax
    -- currentMax never exceeds globalMax
    -- Init: both equal nums[0]!. Pres: globalMax updated to max(globalMax, currentMax).
    invariant "cm_le_gm" currentMax ≤ globalMax
    -- Termination: nums.size - i decreases each iteration
    decreasing nums.size - i
  do
    let val := nums[i]!
    if currentMax + val > val then
      currentMax := currentMax + val
    else
      currentMax := val
    if currentMax > globalMax then
      globalMax := currentMax
    i := i + 1
  return globalMax
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

#assert_same_evaluation #[((MaximumSubarray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MaximumSubarray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MaximumSubarray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MaximumSubarray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MaximumSubarray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MaximumSubarray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MaximumSubarray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MaximumSubarray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MaximumSubarray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MaximumSubarray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0_0
    (nums : Array ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (invariant_gm_witness : ∃ start stop,
  start < stop ∧
    stop ≤ i ∧
      Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0)
          (min stop nums.size - start) =
        globalMax)
    (s : ℕ)
    (hs_lt : s < i)
    : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract s (i + 1)) (OfNat.ofNat 0)
    (min (i + 1) nums.size - s) =
  Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract s i) (OfNat.ofNat 0) (min i nums.size - s) + nums[i]! := by
    have h_i_lt : i < nums.size := if_pos
    have h_min1 : min (i + 1) nums.size = i + 1 := by omega
    have h_min2 : min i nums.size = i := by omega
    have h_sz2 : (nums.extract s i).size = i - s := by
      rw [Array.size_extract, h_min2]
    have h_split : nums.extract s i ++ nums.extract i (i + 1) = nums.extract s (i + 1) := by
      rw [Array.extract_append_extract]
      congr 1 <;> omega
    have h_single : nums.extract i (i + 1) = #[nums[i]] := by
      apply Array.ext
      · simp [Array.size_extract]
        omega
      · intro j h1 h2
        simp [Array.getElem_extract]
        simp [Array.size_extract] at h1
        have hm : min (i + 1) nums.size = i + 1 := by omega
        rw [hm] at h1
        have : j = 0 := by omega
        subst this
        simp
    rw [Array.getElem!_eq_getD, Array.getD, dif_pos h_i_lt]
    rw [h_min1, h_min2]
    rw [← h_split]
    rw [Array.foldl_append' (by rw [h_sz2, Array.size_extract]; simp [h_min1]; omega)]
    rw [h_single]
    simp [Array.foldl_push, Array.foldl_empty]
    congr 1
    omega

theorem goal_0
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = currentMax + nums[i]! := by
    obtain ⟨s, hs_lt, hs_eq⟩ := invariant_cm_witness
    have hs_lt2 : s < i + OfNat.ofNat 1 := by
      have : s < i := hs_lt
      show s < i + OfNat.ofNat 1
      simp [OfNat.ofNat]
      omega
    refine ⟨s, hs_lt2, ?_⟩
    have h_key : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract s (i + 1)) (OfNat.ofNat 0) (min (i + 1) nums.size - s) = Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract s i) (OfNat.ofNat 0) (min i nums.size - s) + nums[i]! := by expose_names; exact (goal_0_0 nums globalMax i if_pos invariant_gm_witness s hs_lt)
    simp only [OfNat.ofNat] at *
    rw [h_key, hs_eq]

theorem goal_1_0
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (start : ℕ)
    (if_pos : start < nums.size)
    (invariant_cm_witness : ∃ start_1 < start,
  Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start_1 start) (OfNat.ofNat 0)
      (min start nums.size - start_1) =
    currentMax)
    (invariant_gm_witness : ∃ start_1 stop,
  start_1 < stop ∧
    stop ≤ start ∧
      Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start_1 stop) (OfNat.ofNat 0)
          (min stop nums.size - start_1) =
        globalMax)
    : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (start + OfNat.ofNat 1)) (OfNat.ofNat 0)
    (min (start + OfNat.ofNat 1) nums.size - start) =
  nums[start]! := by
    have hlt : start < nums.size := if_pos
    have hle1 : start + 1 ≤ nums.size := hlt
    -- Step 1: convert bounded foldl to unbounded foldl on the extract
    have step1 : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (start + OfNat.ofNat 1)) (OfNat.ofNat 0)
      (min (start + OfNat.ofNat 1) nums.size - start) =
      (nums.extract start (start + 1)).foldl (fun (acc : ℤ) (x : ℤ) => acc + x) 0 := by
      rw [Array.foldl_eq_foldlM, Array.foldlM_start_stop, Array.extract_extract]
      simp [Nat.min_eq_left hle1]
    rw [step1]
    -- Convert extract to singleton array #[nums[start]]
    have hsz : (nums.extract start (start + 1)).size = 1 := by
      simp [Array.size_extract, Nat.min_eq_left hle1]
    have hget : (nums.extract start (start + 1))[0]'(by omega) = nums[start]'hlt := by
      rw [Array.getElem_extract]; simp
    have hext_eq : nums.extract start (start + 1) = #[nums[start]'hlt] := by
      apply Array.ext
      · simp [hsz]
      · intro i hi1 hi2
        simp at hi2
        have hi0 : i = 0 := by omega
        subst hi0
        simp [hget]
    rw [hext_eq]
    -- foldl over singleton: use List.foldl_toArray
    have : (#[nums[start]'hlt] : Array ℤ).foldl (fun (acc : ℤ) (x : ℤ) => acc + x) 0 = 0 + nums[start]'hlt := by
      change [nums[start]'hlt].toArray.foldl (fun (acc : ℤ) (x : ℤ) => acc + x) 0 = _
      rw [List.foldl_toArray]
      simp [List.foldl]
    rw [this]
    simp
    -- Now: nums[start] = nums[start]!
    symm
    rw [Array.getElem!_eq_getD, Array.getD]
    simp [hlt]

theorem goal_1
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_pos_1 : OfNat.ofNat 0 < currentMax)
    (if_pos_2 : globalMax < currentMax + nums[i]!)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ currentMax + nums[i]! := by
    intro start hstart
    have hle : start ≤ i := by
      have : (OfNat.ofNat 1 : ℕ) = 1 := rfl
      rw [this] at hstart
      omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · -- Case start < i
      have h_rewrite := goal_0_0 nums globalMax i if_pos invariant_gm_witness start hlt
      have h1 : (OfNat.ofNat 1 : ℕ) = 1 := rfl
      rw [h1] at h_rewrite ⊢
      rw [h_rewrite]
      have h_cm := invariant_cm_max start hlt
      linarith
    · -- Case start = i
      subst heq
      have h_single : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (start + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (start + OfNat.ofNat 1) nums.size - start) = nums[start]! := by expose_names; exact (goal_1_0 nums currentMax globalMax start if_pos invariant_cm_witness invariant_gm_witness)
      rw [h_single]
      linarith

theorem goal_2
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    : ∃ start stop, start < stop ∧ stop ≤ i + OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = currentMax + nums[i]! := by
    obtain ⟨s, hs_lt, hs_eq⟩ := invariant_cm_witness
    exact ⟨s, i + 1, by omega, by show i + 1 ≤ i + OfNat.ofNat 1; simp [OfNat.ofNat], by rw [goal_0_0 nums globalMax i if_pos invariant_gm_witness s hs_lt, hs_eq]⟩

theorem goal_3
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_pos_1 : OfNat.ofNat 0 < currentMax)
    (if_pos_2 : globalMax < currentMax + nums[i]!)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ currentMax + nums[i]! := by
    intro start stop hlt hle
    -- Case split: stop ≤ i or stop = i + 1
    rcases Nat.eq_or_lt_of_le hle with h | h
    · -- stop = i + 1
      subst h
      -- Sub-case: start < i or start = i
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with heq | hlt'
      · -- start = i, stop = i + 1: single element nums[i]!
        subst heq
        -- Need: foldl over extract(i, i+1) = nums[i]!
        have h1 : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (start + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (start + OfNat.ofNat 1) nums.size - start) = nums[start]! :=
          goal_1_0 nums currentMax globalMax start if_pos invariant_cm_witness invariant_gm_witness
        linarith
      · -- start < i, stop = i + 1
        have h1 := goal_0_0 nums globalMax i if_pos invariant_gm_witness start hlt'
        have h2 := invariant_cm_max start hlt'
        linarith
    · -- stop < i + 1, i.e. stop ≤ i
      have hle' : stop ≤ i := Nat.lt_succ_iff.mp h
      have h1 := invariant_gm_max start stop hlt hle'
      linarith

theorem goal_4
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = currentMax + nums[i]! := by
    intros; expose_names; exact
        goal_0 nums currentMax globalMax i if_pos invariant_cm_witness invariant_gm_witness

theorem goal_5
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_pos_1 : OfNat.ofNat 0 < currentMax)
    (if_neg : currentMax + nums[i]! ≤ globalMax)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ currentMax + nums[i]! := by
    intro start hstart
    rw [Nat.lt_add_one_iff] at hstart
    rcases Nat.lt_or_eq_of_le hstart with h | h
    · -- start < i: use goal_0_0 and invariant_cm_max
      have hrewrite := goal_0_0 nums globalMax i if_pos invariant_gm_witness start h
      rw [hrewrite]
      have hle := invariant_cm_max start h
      linarith
    · -- start = i: sum is nums[i]!, need nums[i]! ≤ currentMax + nums[i]!
      subst h
      have hrewrite := goal_1_0 nums currentMax globalMax start if_pos invariant_cm_witness invariant_gm_witness
      rw [hrewrite]
      linarith

theorem goal_6
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_pos_1 : OfNat.ofNat 0 < currentMax)
    (if_neg : currentMax + nums[i]! ≤ globalMax)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax := by
    intro start stop hlt hle
    by_cases h : stop ≤ i
    · exact invariant_gm_max start stop hlt h
    · have hstop : stop = i + 1 := by
        have : (OfNat.ofNat 1 : ℕ) = 1 := rfl
        omega
      subst hstop
      have h5 := goal_5 nums currentMax globalMax i invariant_i_lower invariant_i_upper if_pos invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_pos_1 if_neg start hlt
      linarith

theorem goal_7
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = nums[i]! := by
    have key : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract i (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - i) = nums[i]! := by
      exact goal_1_0 nums currentMax globalMax i if_pos invariant_cm_witness invariant_gm_witness
    have hlt : i < i + OfNat.ofNat 1 := by
      show i < i + 1
      omega
    exact ⟨i, hlt, key⟩

theorem goal_8
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_pos_1 : globalMax < nums[i]!)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ nums[i]! := by
    sorry



theorem goal_8
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_pos_1 : globalMax < nums[i]!)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ nums[i]! := by
    sorry

theorem goal_9
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_pos_1 : globalMax < nums[i]!)
    : ∃ start stop, start < stop ∧ stop ≤ i + OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = nums[i]! := by
    sorry

theorem goal_10
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_pos_1 : globalMax < nums[i]!)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ nums[i]! := by
    sorry

theorem goal_11
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_neg_1 : nums[i]! ≤ globalMax)
    : ∃ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) = nums[i]! := by
    sorry

theorem goal_12
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_neg_1 : nums[i]! ≤ globalMax)
    : ∀ start < i + OfNat.ofNat 1, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size - start) ≤ nums[i]! := by
    sorry

theorem goal_13
    (nums : Array ℤ)
    (currentMax : ℤ)
    (globalMax : ℤ)
    (i : ℕ)
    (invariant_i_lower : OfNat.ofNat 1 ≤ i)
    (invariant_i_upper : i ≤ nums.size)
    (invariant_cm_le_gm : currentMax ≤ globalMax)
    (if_pos : i < nums.size)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_cm_witness : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = currentMax)
    (invariant_cm_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ currentMax)
    (invariant_gm_witness : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = globalMax)
    (invariant_gm_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax)
    (if_neg : currentMax ≤ OfNat.ofNat 0)
    (if_neg_1 : nums[i]! ≤ globalMax)
    : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ globalMax := by
    sorry

theorem goal_14
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) = nums[OfNat.ofNat 0]! := by
    sorry

theorem goal_15
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) ≤ nums[OfNat.ofNat 0]! := by
    sorry

theorem goal_16
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : ∃ start stop, start < stop ∧ stop ≤ OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = nums[OfNat.ofNat 0]! := by
    sorry

theorem goal_17
    (nums : Array ℤ)
    (require_1 : OfNat.ofNat 0 < nums.size)
    : ∀ (start stop : ℕ), start < stop → stop ≤ OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ nums[OfNat.ofNat 0]! := by
    sorry



prove_correct MaximumSubarray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums currentMax globalMax i if_pos invariant_cm_witness invariant_gm_witness)
  exact (goal_1 nums currentMax globalMax i invariant_i_lower invariant_i_upper if_pos invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_pos_1 if_pos_2)
  exact (goal_2 nums currentMax globalMax i if_pos invariant_cm_witness invariant_gm_witness)
  exact (goal_3 nums currentMax globalMax i invariant_i_lower invariant_i_upper if_pos invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_pos_1 if_pos_2)
  exact (goal_4 nums currentMax globalMax i if_pos invariant_cm_witness invariant_gm_witness)
  exact (goal_5 nums currentMax globalMax i invariant_i_lower invariant_i_upper if_pos invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_pos_1 if_neg)
  exact (goal_6 nums currentMax globalMax i invariant_i_lower invariant_i_upper if_pos invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_pos_1 if_neg)
  exact (goal_7 nums currentMax globalMax i if_pos invariant_cm_witness invariant_gm_witness)
  exact (goal_8 nums currentMax globalMax i invariant_i_lower invariant_i_upper invariant_cm_le_gm if_pos require_1 invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_neg if_pos_1)
  exact (goal_9 nums currentMax globalMax i invariant_i_lower invariant_i_upper invariant_cm_le_gm if_pos require_1 invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_neg if_pos_1)
  exact (goal_10 nums currentMax globalMax i invariant_i_lower invariant_i_upper invariant_cm_le_gm if_pos require_1 invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_neg if_pos_1)
  exact (goal_11 nums currentMax globalMax i invariant_i_lower invariant_i_upper invariant_cm_le_gm if_pos require_1 invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_neg if_neg_1)
  exact (goal_12 nums currentMax globalMax i invariant_i_lower invariant_i_upper invariant_cm_le_gm if_pos require_1 invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_neg if_neg_1)
  exact (goal_13 nums currentMax globalMax i invariant_i_lower invariant_i_upper invariant_cm_le_gm if_pos require_1 invariant_cm_witness invariant_cm_max invariant_gm_witness invariant_gm_max if_neg if_neg_1)
  exact (goal_14 nums require_1)
  exact (goal_15 nums require_1)
  exact (goal_16 nums require_1)
  exact (goal_17 nums require_1)
end Proof
