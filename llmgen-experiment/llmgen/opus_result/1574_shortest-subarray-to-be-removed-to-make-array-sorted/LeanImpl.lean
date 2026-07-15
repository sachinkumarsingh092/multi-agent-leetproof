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
    ShortestSubarrayToRemoveToMakeArraySorted: Given an integer array, remove a contiguous subarray
    (possibly empty) so that the remaining elements are non-decreasing, and return the minimum
    removed length.

    Natural language breakdown:
    1. Input is an array of integers `arr`.
    2. We may remove a contiguous subarray `arr[l..r)` (with 0 ≤ l ≤ r ≤ n). The removed subarray
       can be empty (l = r) and can also be the whole array.
    3. After removing `arr[l..r)`, the remaining elements preserve their relative order and form
       the concatenation of the prefix `arr[0..l)` and suffix `arr[r..n)`.
    4. The remaining array must be non-decreasing: for every adjacent pair of elements,
       the earlier element is ≤ the later element.
    5. The result is the minimum possible length (r - l) among all valid removals.
    6. Edge cases:
       - Already non-decreasing arrays allow removing the empty subarray, so the answer can be 0.
       - Empty array is already non-decreasing, so answer is 0.
       - If the array is strictly decreasing, we can keep at most one element, so the answer is n-1.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper: non-decreasing predicate over adjacent indices.
def isNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! ≤ arr[i + 1]!

-- Helper: the array resulting from removing the half-open interval [l, r).
def removeSubarray (arr : Array Int) (l : Nat) (r : Nat) : Array Int :=
  arr.extract 0 l ++ arr.extract r arr.size

-- Helper: a removal is valid when indices are in range and the remaining array is non-decreasing.
def validRemoval (arr : Array Int) (l : Nat) (r : Nat) : Prop :=
  l ≤ r ∧ r ≤ arr.size ∧ isNondecreasing (removeSubarray arr l r)

-- Precondition: no restrictions; empty removals are allowed, so every array has an answer.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the minimum possible removed length among all valid removals.
def postcondition (arr : Array Int) (result : Nat) : Prop :=
  (∃ (l : Nat) (r : Nat), validRemoval arr l r ∧ result = r - l) ∧
  (∀ (l : Nat) (r : Nat), validRemoval arr l r → result ≤ r - l)
end Specs

section Impl
def implementation (arr : Array Int) : Nat :=
  let n := arr.size
  if n ≤ 1 then 0
  else
    -- Find longest non-decreasing prefix: find first index where arr[i] > arr[i+1]
    let rec findPrefixEnd (i : Nat) : Nat :=
      if h : i + 1 < n then
        if arr[i]! ≤ arr[i + 1]! then findPrefixEnd (i + 1)
        else i
      else i
    termination_by n - i
    let prefixEnd := findPrefixEnd 0  -- last index of non-decreasing prefix

    -- If entire array is non-decreasing
    if prefixEnd == n - 1 then 0
    else
      -- Find longest non-decreasing suffix: find last index where arr[i-1] > arr[i]
      let rec findSuffixStart (j : Nat) : Nat :=
        if h : j = 0 then 0
        else if arr[j - 1]! ≤ arr[j]! then findSuffixStart (j - 1)
        else j
      termination_by j
      decreasing_by omega
      let suffixStart := findSuffixStart (n - 1)  -- first index of non-decreasing suffix

      -- Option 1: keep only prefix (remove from prefixEnd+1 to end)
      let ans1 := n - (prefixEnd + 1)
      -- Option 2: keep only suffix (remove from 0 to suffixStart)
      let ans2 := suffixStart
      let initAns := min ans1 ans2

      -- Option 3: merge prefix and suffix using two pointers
      -- i scans prefix [0..prefixEnd], j scans suffix [suffixStart..n-1]
      -- We want arr[i] <= arr[j], and remove (i+1)..(j-1), length = j - i - 1
      let rec merge (i j best : Nat) : Nat :=
        if h1 : i > prefixEnd then best
        else if h2 : j ≥ n then best
        else
          if arr[i]! ≤ arr[j]! then
            let removal := j - (i + 1)
            let best' := min best removal
            merge (i + 1) j best'
          else
            merge i (j + 1) best
      termination_by (prefixEnd + 1 - i) + (n - j)
      decreasing_by all_goals omega
      merge 0 suffixStart initAns
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [1,2,3,10,4,2,3,5] => expected 3
-- One optimal removal is [10,4,2].
def test1_arr : Array Int := #[1, 2, 3, 10, 4, 2, 3, 5]
def test1_Expected : Nat := 3

-- Test case 2: Example 2 (strictly decreasing)
-- arr = [5,4,3,2,1] => expected 4

def test2_arr : Array Int := #[5, 4, 3, 2, 1]
def test2_Expected : Nat := 4

-- Test case 3: Example 3 (already sorted)
-- arr = [1,2,3] => expected 0

def test3_arr : Array Int := #[1, 2, 3]
def test3_Expected : Nat := 0

-- Test case 4: Empty array (degenerate)
-- Already non-decreasing; remove nothing.

def test4_arr : Array Int := #[]
def test4_Expected : Nat := 0

-- Test case 5: Singleton array
-- Already non-decreasing.

def test5_arr : Array Int := #[42]
def test5_Expected : Nat := 0

-- Test case 6: Two elements already non-decreasing

def test6_arr : Array Int := #[1, 1]
def test6_Expected : Nat := 0

-- Test case 7: Two elements decreasing
-- Must remove one element.

def test7_arr : Array Int := #[2, 1]
def test7_Expected : Nat := 1

-- Test case 8: Needs removal in the middle; minimal is 1 (remove the 3)
-- [1,2,3,2,4] -> remove [3] gives [1,2,2,4]

def test8_arr : Array Int := #[1, 2, 3, 2, 4]
def test8_Expected : Nat := 1

-- Test case 9: Remove a prefix to become sorted; minimal is 2
-- [3,4,1,2] -> remove [3,4] leaves [1,2]

def test9_arr : Array Int := #[3, 4, 1, 2]
def test9_Expected : Nat := 2
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
-- Lean wrapper for velvet_plausible_test failed to compile. Giving up on PBT.

-- method implementationPbt (arr : Array Int)
--   return (result : Nat)
--   require precondition arr
--   ensures postcondition arr result
--   do
--   return (implementation arr)

-- velvet_plausible_test implementationPbt (config := { maxMs := some 5000 })
end Pbt

section Proof
theorem correctness_goal_0_0
    (arr : Array ℤ)
    : validRemoval arr 0 arr.size := by
    unfold validRemoval
    refine ⟨Nat.zero_le _, le_refl _, ?_⟩
    unfold removeSubarray
    have h1 : arr.extract 0 0 = #[] := by
      rw [Array.extract_eq_empty_iff]; simp
    have h2 : arr.extract arr.size arr.size = #[] := by
      rw [Array.extract_eq_empty_iff]; simp
    rw [h1, h2, Array.empty_append]
    unfold isNondecreasing
    intro i hi
    simp at hi

theorem correctness_goal_0_1
    (arr : Array ℤ)
    : arr.size ≤ 1 → isNondecreasing arr := by
    intro h
    unfold isNondecreasing
    intro i hi
    omega

theorem validRemoval_empty (arr : Array ℤ) (h : isNondecreasing arr) : validRemoval arr 0 0 := by
  unfold validRemoval
  refine ⟨le_refl 0, Nat.zero_le _, ?_⟩
  unfold removeSubarray
  have h1 : arr.extract 0 0 = #[] := by
    rw [Array.extract_eq_empty_iff]
    omega
  rw [h1, Array.empty_append, Array.extract_size]
  exact h

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findPrefixEnd_le (arr : Array ℤ) (n : Nat) (i : Nat) :
    i ≤ implementation.findPrefixEnd arr n i := by
  unfold implementation.findPrefixEnd
  split
  · split
    · have ih := findPrefixEnd_le arr n (i + 1)
      omega
    · omega
  · omega

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findPrefixEnd_lt (arr : Array ℤ) (n : Nat) (i : Nat) (hi : i < n) :
    implementation.findPrefixEnd arr n i < n := by
  unfold implementation.findPrefixEnd
  split
  · split
    · exact findPrefixEnd_lt arr n (i + 1) (by omega)
    · omega
  · omega

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findPrefixEnd_nondec (arr : Array ℤ) (n : Nat) (hn : n = arr.size) (i : Nat) (hi : i < n) 
    (hprev : ∀ k, k < i → k + 1 < n → arr[k]! ≤ arr[k+1]!) :
    ∀ k, k < implementation.findPrefixEnd arr n i → k + 1 < n → arr[k]! ≤ arr[k+1]! := by
  unfold implementation.findPrefixEnd
  split
  case isTrue h1 =>
    split
    case isTrue h2 =>
      -- arr[i] ≤ arr[i+1], recurse with i+1
      apply findPrefixEnd_nondec arr n hn (i + 1) (by omega)
      intro k hk hk2
      by_cases hki : k < i
      · exact hprev k hki hk2
      · have : k = i := by omega
        subst this
        exact h2
    case isFalse h2 =>
      -- arr[i] > arr[i+1], return i
      intro k hk hk2
      exact hprev k hk hk2
  case isFalse h1 =>
    intro k hk hk2
    exact hprev k hk hk2

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findPrefixEnd_boundary (arr : Array ℤ) (n : Nat) (hn : n = arr.size) (i : Nat) (hi : i < n) :
    let p := implementation.findPrefixEnd arr n i
    p + 1 < n → ¬ (arr[p]! ≤ arr[p+1]!) := by
  unfold implementation.findPrefixEnd
  split
  case isTrue h1 =>
    split
    case isTrue h2 =>
      exact findPrefixEnd_boundary arr n hn (i + 1) (by omega)
    case isFalse h2 =>
      simp only
      intro _
      exact h2
  case isFalse h1 =>
    simp only
    intro h
    omega

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findPrefixEnd_full_means_sorted (arr : Array ℤ) (n : Nat) (hn : n = arr.size) (hn1 : ¬ n ≤ 1)
    (h : (implementation.findPrefixEnd arr n 0 == n - 1) = true) :
    isNondecreasing arr := by
  have hpe : implementation.findPrefixEnd arr n 0 = n - 1 := by
    simp [beq_iff_eq] at h; exact h
  unfold isNondecreasing
  intro i hi
  have := findPrefixEnd_nondec arr n hn 0 (by omega) (by intro k hk; omega)
  have hle : i < implementation.findPrefixEnd arr n 0 := by omega
  exact this i hle (by omega)

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findSuffixStart_le (arr : Array ℤ) (j : Nat) (hj : j < arr.size) :
    implementation.findSuffixStart arr j ≤ j := by
  unfold implementation.findSuffixStart
  split
  case isTrue h =>
    subst h; omega
  case isFalse h =>
    split
    case isTrue h2 =>
      have ih := findSuffixStart_le arr (j - 1) (by omega)
      omega
    case isFalse h2 =>
      omega

set_option maxRecDepth 1000 in
set_option maxHeartbeats 20000000 in
private theorem findSuffixStart_nondec (arr : Array ℤ) (j : Nat) (hj : j < arr.size) 
    (hpost : ∀ k, j ≤ k → k + 1 < arr.size → arr[k]! ≤ arr[k+1]!) :
    ∀ k, implementation.findSuffixStart arr j ≤ k → k + 1 < arr.size → arr[k]! ≤ arr[k+1]! := by
  unfold implementation.findSuffixStart
  split
  case isTrue h =>
    subst h
    intro k hk hk2
    exact hpost k hk hk2
  case isFalse h =>
    split
    case isTrue h2 =>
      apply findSuffixStart_nondec arr (j - 1) (by omega)
      intro k hk hk2
      by_cases hkj : j ≤ k
      · exact hpost k hkj hk2
      · have hkeq : k = j - 1 := by omega
        subst hkeq
        have : j - 1 + 1 = j := by omega
        rw [this]
        convert h2 using 2
    case isFalse h2 =>
      intro k hk hk2
      exact hpost k hk hk2

set_option maxRecDepth 1000 in
set_option maxHeartbeats 40000000 in
private theorem prefix_removal_valid (arr : Array ℤ) (p : Nat) (hp : p < arr.size)
    (hnd : ∀ k, k ≤ p → k + 1 < arr.size → arr[k]! ≤ arr[k+1]!)
    : validRemoval arr (p + 1) arr.size := by
  unfold validRemoval
  refine ⟨by omega, le_refl _, ?_⟩
  unfold removeSubarray
  have hempty : arr.extract arr.size arr.size = #[] := by
    rw [Array.extract_empty_of_size_le_start (by omega)]
  rw [hempty, Array.append_empty]
  unfold isNondecreasing
  intro i hi
  have hext_size : (arr.extract 0 (p + 1)).size = p + 1 := by
    rw [Array.size_extract]; omega
  rw [hext_size] at hi
  -- We need: (arr.extract 0 (p + 1))[i]! ≤ (arr.extract 0 (p + 1))[i + 1]!
  -- Since i + 1 < p + 1, both i and i+1 are in bounds for the extract
  have hi_bound : i < (arr.extract 0 (p + 1)).size := by rw [hext_size]; omega
  have hi1_bound : i + 1 < (arr.extract 0 (p + 1)).size := by rw [hext_size]; omega
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  simp [Array.getD, hi_bound, hi1_bound, Array.getElem_extract]
  -- Now we have arr[0 + i] ≤ arr[0 + (i + 1)]
  -- which is arr[i] ≤ arr[i+1]
  have := hnd i (by omega) (by omega)
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD] at this
  simp [Array.getD] at this ⊢
  convert this using 2 <;> omega

set_option maxRecDepth 1000 in
set_option maxHeartbeats 40000000 in
private theorem suffix_removal_valid (arr : Array ℤ) (s : Nat) (hs : s ≤ arr.size)
    (hnd : ∀ k, s ≤ k → k + 1 < arr.size → arr[k]! ≤ arr[k+1]!)
    : validRemoval arr 0 s := by
  unfold validRemoval
  refine ⟨Nat.zero_le _, hs, ?_⟩
  unfold removeSubarray
  have hempty : arr.extract 0 0 = #[] := by
    rw [Array.extract_eq_empty_iff]; omega
  rw [hempty, Array.empty_append]
  unfold isNondecreasing
  intro i hi
  have hext_size : (arr.extract s arr.size).size = arr.size - s := by
    rw [Array.size_extract]; omega
  rw [hext_size] at hi
  have hi_bound : i < (arr.extract s arr.size).size := by rw [hext_size]; omega
  have hi1_bound : i + 1 < (arr.extract s arr.size).size := by rw [hext_size]; omega
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  simp [Array.getD, hi_bound, hi1_bound, Array.getElem_extract]
  have := hnd (s + i) (by omega) (by omega)
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD] at this
  simp [Array.getD] at this ⊢
  convert this using 2 <;> omega


theorem correctness_goal_0_2
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h_valid_all : validRemoval arr 0 arr.size)
    (h_small_sorted : arr.size ≤ 1 → isNondecreasing arr)
    : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l := by
    sorry


theorem correctness_goal_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l := by
    -- Key insight: validRemoval arr 0 arr.size always holds (removing everything leaves empty array)
    -- and the implementation result is always ≤ arr.size.
    -- But we need to match the exact implementation value.
    --
    -- Alternative: We can always use (0, arr.size) as fallback, giving removal = arr.size.
    -- The implementation returns ≤ arr.size in all cases.
    -- But we need equality, not ≤.
    --
    -- Let me just prove a comprehensive helper that handles all cases.
    -- For the easy cases (n ≤ 1, already sorted): witness is (0, 0).
    -- For the main case: we need loop invariant analysis.
    --
    -- Actually, let's try to just prove the key helper lemmas that the subgoal provers can use.
    
    -- Helper 1: removing everything is valid
    have h_valid_all : validRemoval arr 0 arr.size := by expose_names; exact (correctness_goal_0_0 arr)
    
    -- Helper 2: isNondecreasing of removeSubarray arr l r when prefix [0..l) and suffix [r..n) are 
    -- both non-decreasing and (if both non-empty) arr[l-1] ≤ arr[r]
    -- This is the core structural lemma.
    
    -- Helper 3: For arr.size ≤ 1, the array is non-decreasing  
    have h_small_sorted : arr.size ≤ 1 → isNondecreasing arr := by expose_names; exact (correctness_goal_0_1 arr)
    
    -- Main: construct the existential witness
    -- For n ≤ 1: implementation returns 0, use (0,0) since arr is non-decreasing
    -- For sorted arr: implementation returns 0, use (0,0)
    -- For non-trivial: the merge phase finds a valid (l,r)
    have h_main : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l := by expose_names; exact (correctness_goal_0_2 arr h_precond h_valid_all h_small_sorted)
    exact h_main

theorem correctness_goal_1_0
    (arr : Array ℤ)
    (h_small : arr.size ≤ 1)
    : implementation arr = 0 := by
    unfold implementation
    simp [h_small]

theorem correctness_goal_1_1
    (arr : Array ℤ)
    (h_small : ¬arr.size ≤ 1)
    (h_sorted : (implementation.findPrefixEnd arr arr.size 0 == arr.size - 1) = true)
    : implementation arr = 0 := by
    unfold implementation
    simp [h_small, h_sorted]

theorem correctness_goal_1_2
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h_exists : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l)
    (l : ℕ)
    (r : ℕ)
    (hvalid : validRemoval arr l r)
    (h_small : ¬arr.size ≤ 1)
    (h_sorted : ¬(implementation.findPrefixEnd arr arr.size 0 == arr.size - 1) = true)
    : implementation arr ≤ r - l := by
    sorry

theorem correctness_goal_1
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h_exists : ∃ l r, validRemoval arr l r ∧ implementation arr = r - l)
    : ∀ (l r : ℕ), validRemoval arr l r → implementation arr ≤ r - l := by
    intro l r hvalid
    -- Case split on whether array is small
    by_cases h_small : arr.size ≤ 1
    · -- When n ≤ 1, implementation returns 0
      have h1 : implementation arr = 0 := by expose_names; exact (correctness_goal_1_0 arr h_small)
      rw [h1]; exact Nat.zero_le _
    · push_neg at h_small
      -- Case split on whether array is already sorted
      by_cases h_sorted : (implementation.findPrefixEnd arr arr.size 0 == arr.size - 1) = true
      · -- When fully sorted, implementation returns 0
        have h2 : implementation arr = 0 := by expose_names; exact (correctness_goal_1_1 arr h_small h_sorted)
        rw [h2]; exact Nat.zero_le _
      · -- The main case: array is not fully sorted
        -- Here the implementation computes merge 0 suffixStart (min ans1 ans2)
        -- We need to show this ≤ r - l
        have h3 : implementation arr ≤ r - l := by expose_names; exact (correctness_goal_1_2 arr h_precond h_exists l r hvalid h_small h_sorted)
        exact h3


theorem correctness_goal
    (arr : Array Int)
    (h_precond : precondition arr)
    : postcondition arr (implementation arr) := by
    unfold postcondition
    have h_exists : ∃ (l : Nat) (r : Nat), validRemoval arr l r ∧ implementation arr = r - l := by expose_names; exact (correctness_goal_0 arr h_precond)
    have h_optimal : ∀ (l : Nat) (r : Nat), validRemoval arr l r → implementation arr ≤ r - l := by expose_names; exact (correctness_goal_1 arr h_precond h_exists)
    exact ⟨h_exists, h_optimal⟩
end Proof
