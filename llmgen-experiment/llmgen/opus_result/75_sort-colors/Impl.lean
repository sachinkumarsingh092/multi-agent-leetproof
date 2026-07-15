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
    SortColors: Given an array of colors encoded as 0, 1, 2, reorder it so that all 0s come first,
    then all 1s, then all 2s.
    Natural language breakdown:
    1. The input is an array `nums` of natural numbers that represent colors.
    2. Only the values 0, 1, and 2 are valid colors.
    3. The output must have the same length as the input.
    4. The output must contain the same multiset of elements as the input (no loss/duplication).
    5. The output must be ordered so that every 0 appears before every 1 and every 1 before every 2.
    6. Equivalently, there exist boundaries a ≤ b such that indices < a are 0, indices in [a,b) are 1,
       and indices ≥ b are 2.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

section Specs
-- Helper: all entries are in {0,1,2}
def ColorsOnly (nums : Array Nat) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≤ 2

-- Helper: array is partitioned into 0s then 1s then 2s
-- This avoids referencing any particular algorithm while fully characterizing the desired order.
def Is012Sorted (nums : Array Nat) : Prop :=
  ∃ (a : Nat) (b : Nat),
    a ≤ b ∧ b ≤ nums.size ∧
    (∀ (i : Nat), i < a → nums[i]! = 0) ∧
    (∀ (i : Nat), a ≤ i ∧ i < b → nums[i]! = 1) ∧
    (∀ (i : Nat), b ≤ i ∧ i < nums.size → nums[i]! = 2)

-- Helper: count occurrences of a value in an array
-- (Array.count is available when DecidableEq is available.)
def countVal (nums : Array Nat) (v : Nat) : Nat :=
  nums.count v

-- Preconditions: input must contain only 0/1/2.
def precondition (nums : Array Nat) : Prop :=
  ColorsOnly nums

-- Postconditions: result has same size, is ordered as 0-then-1-then-2,
-- and preserves the counts of 0,1,2 from the input.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  result.size = nums.size ∧
  Is012Sorted result ∧
  countVal result 0 = countVal nums 0 ∧
  countVal result 1 = countVal nums 1 ∧
  countVal result 2 = countVal nums 2
end Specs

section Impl
method SortColors (nums : Array Nat)
  return (result : Array Nat)
  require precondition nums
  ensures postcondition nums result
  do
    let n := nums.size
    -- Count occurrences of 0, 1, 2
    let mut count0 : Nat := 0
    let mut count1 : Nat := 0
    let mut count2 : Nat := 0
    let mut i : Nat := 0
    while i < n
      -- i is bounded by array size
      invariant "i_bound" 0 ≤ i ∧ i ≤ n
      -- total count equals elements processed so far
      invariant "total_count" count0 + count1 + count2 = i
      -- partial counts match counts in the prefix of nums
      invariant "c0_partial" count0 = (nums.extract 0 i).count 0
      invariant "c1_partial" count1 = (nums.extract 0 i).count 1
      invariant "c2_partial" count2 = (nums.extract 0 i).count 2
      decreasing n - i
    do
      let v := nums[i]!
      if v = 0 then
        count0 := count0 + 1
      else
        if v = 1 then
          count1 := count1 + 1
        else
          count2 := count2 + 1
      i := i + 1
    -- Build result array
    let mut res := Array.replicate n 0
    -- Fill 1s
    let mut j : Nat := count0
    while j < count0 + count1
      -- j is bounded between count0 and count0+count1
      invariant "j_bound" count0 ≤ j ∧ j ≤ count0 + count1
      -- result array size preserved
      invariant "res_size_1" res.size = n
      -- counts sum to n (established after loop 1)
      invariant "count_sum" count0 + count1 + count2 = n
      -- positions before count0 are still 0
      invariant "zeros_intact" ∀ idx, idx < count0 → res[idx]! = 0
      -- positions from count0 to j-1 are filled with 1
      invariant "ones_filled" ∀ idx, count0 ≤ idx ∧ idx < j → res[idx]! = 1
      -- positions from j to n-1 are still 0 (from replicate)
      invariant "rest_zero_1" ∀ idx, j ≤ idx ∧ idx < n → res[idx]! = 0
      -- counts match the full array counts
      invariant "c0_final" count0 = countVal nums 0
      invariant "c1_final" count1 = countVal nums 1
      invariant "c2_final" count2 = countVal nums 2
      decreasing (count0 + count1) - j
    do
      res := res.set! j 1
      j := j + 1
    -- Fill 2s
    let mut k : Nat := count0 + count1
    while k < n
      -- k is bounded between count0+count1 and n
      invariant "k_bound" count0 + count1 ≤ k ∧ k ≤ n
      -- result array size preserved
      invariant "res_size_2" res.size = n
      -- counts sum to n
      invariant "count_sum_2" count0 + count1 + count2 = n
      -- positions before count0 are 0
      invariant "zeros_final" ∀ idx, idx < count0 → res[idx]! = 0
      -- positions from count0 to count0+count1-1 are 1
      invariant "ones_final" ∀ idx, count0 ≤ idx ∧ idx < count0 + count1 → res[idx]! = 1
      -- positions from count0+count1 to k-1 are 2
      invariant "twos_filled" ∀ idx, count0 + count1 ≤ idx ∧ idx < k → res[idx]! = 2
      -- positions from k to n-1 are still 0
      invariant "rest_zero_2" ∀ idx, k ≤ idx ∧ idx < n → res[idx]! = 0
      -- counts match the full array counts
      invariant "c0_final_2" count0 = countVal nums 0
      invariant "c1_final_2" count1 = countVal nums 1
      invariant "c2_final_2" count2 = countVal nums 2
      decreasing n - k
    do
      res := res.set! k 2
      k := k + 1
    return res
end Impl

section TestCases
-- Test case 1: Example 1 from the problem statement
-- Input: [2,0,2,1,1,0] Output: [0,0,1,1,2,2]
def test1_nums : Array Nat := #[2, 0, 2, 1, 1, 0]
def test1_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 2: Example 2 from the problem statement
-- Input: [2,0,1] Output: [0,1,2]
def test2_nums : Array Nat := #[2, 0, 1]
def test2_Expected : Array Nat := #[0, 1, 2]

-- Test case 3: Empty array (degenerate but valid)
def test3_nums : Array Nat := #[]
def test3_Expected : Array Nat := #[]

-- Test case 4: Singleton 0
def test4_nums : Array Nat := #[0]
def test4_Expected : Array Nat := #[0]

-- Test case 5: Singleton 1
def test5_nums : Array Nat := #[1]
def test5_Expected : Array Nat := #[1]

-- Test case 6: Singleton 2
def test6_nums : Array Nat := #[2]
def test6_Expected : Array Nat := #[2]

-- Test case 7: Already sorted with repeats
def test7_nums : Array Nat := #[0, 0, 1, 1, 2, 2]
def test7_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 8: Reverse sorted
def test8_nums : Array Nat := #[2, 2, 1, 1, 0, 0]
def test8_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 9: Mixed small (extra diversity)
def test9_nums : Array Nat := #[1, 0, 2, 0, 1]
def test9_Expected : Array Nat := #[0, 0, 1, 1, 2]

-- Recommend to validate: precondition, postcondition, SortColors
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((SortColors test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SortColors test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SortColors test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SortColors test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SortColors test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SortColors test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SortColors test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SortColors test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SortColors test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test SortColors (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + OfNat.ofNat 1 = Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    have h1 : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
      have := @Array.push_extract_getElem ℕ nums 0 i if_pos
      simp only [Nat.min_eq_left (Nat.zero_le i)] at this
      exact this
    have h_getelem : nums[i]! = nums[i] := by
      rw [Array.getElem!_eq_getD]
      unfold Array.getD
      simp only [dif_pos if_pos]
      unfold Array.getInternal
      rfl
    have h_eq : (nums[i] : ℕ) = 0 := by rw [← h_getelem]; exact if_pos_1
    rw [← h1, h_eq, Array.count_push_self]

theorem goal_1
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = i)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    have h1 : (nums.extract 0 i).push nums[i] = nums.extract (min 0 i) (i + 1) :=
      Array.push_extract_getElem if_pos
    have h2 : min 0 i = 0 := by omega
    rw [h2] at h1
    rw [← h1]
    have h3 : nums[i]! = nums[i] := getElem!_pos nums i if_pos
    have h4 : nums[i] ≠ 1 := by
      intro heq
      rw [heq] at h3
      simp [h3] at if_pos_1
    exact (Array.count_push_of_ne h4).symm

theorem goal_2
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = i)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    -- Normalize OfNat.ofNat to actual literals
    change Array.count 2 (nums.extract 0 i) = Array.count 2 (nums.extract 0 (i + 1))
    -- The key fact: extract 0 (i+1) = extract 0 i ++ extract i (i+1)
    have h_split : nums.extract 0 (i + 1) = nums.extract 0 i ++ nums.extract i (i + 1) := by
      have h := @Array.extract_append_extract _ nums 0 i (i + 1)
      simp only [Nat.zero_le, Nat.min_eq_left, Nat.le_succ, Nat.max_eq_right] at h
      exact h.symm
    rw [h_split, Array.count_append]
    -- Suffices to show count of 2 in the singleton slice is 0
    suffices h : Array.count 2 (nums.extract i (i + 1)) = 0 by omega
    rw [Array.count_eq_zero]
    intro hmem
    rw [Array.mem_extract_iff_getElem] at hmem
    obtain ⟨k, hk, hval⟩ := hmem
    have hsz : (nums.extract i (i + 1)).size = min (i + 1) nums.size - i := Array.size_extract ..
    have hk0 : k = 0 := by
      have : min (i + 1) nums.size - i ≤ 1 := by omega
      omega
    subst hk0
    simp at hval
    -- hval : nums[i] = 2
    -- if_pos_1 : nums[i]! = 0
    have h_bang : nums[i]! = nums[i]'if_pos := by
      simp only [getElem!_pos, if_pos]
    rw [h_bang] at if_pos_1
    -- if_pos_1 : nums[i]'if_pos = 0
    -- hval : nums[i] = 2
    -- These are the same nums[i], contradiction
    rw [if_pos_1] at hval
    exact absurd hval (by decide)

theorem goal_3
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = i)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    have hmin : min 0 i = 0 := by omega
    have h1 : (nums.extract 0 i).push nums[i] = nums.extract (min 0 i) (i + 1) :=
      Array.push_extract_getElem if_pos
    rw [hmin] at h1
    -- h1 : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1)
    have h2 : nums[i]! = nums[i] := by
      simp [Array.getElem!_eq_getD, Array.getD, if_pos]
    have h4 : nums[i] ≠ 0 := by
      intro heq; apply if_neg; rw [h2, heq]
    have h5 : Array.count 0 ((nums.extract 0 i).push nums[i]) = Array.count 0 (nums.extract 0 i) :=
      Array.count_push_of_ne h4
    rw [h1] at h5
    exact h5.symm

theorem goal_4
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + OfNat.ofNat 1 = Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    have h1 := @Array.push_extract_getElem _ nums 0 i if_pos
    rw [Nat.zero_min] at h1
    have h_val : (nums[i] : ℕ) = 1 := by
      have : nums[i]! = (nums[i] : ℕ) := by simp [getElem!_pos, if_pos]
      linarith [if_pos_1]
    conv_rhs => rw [show (OfNat.ofNat 0 : ℕ) = 0 from rfl, show (OfNat.ofNat 1 : ℕ) = 1 from rfl]
    rw [← h1, h_val, Array.count_push_self]

theorem goal_5
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    -- push_extract_getElem: (as.extract i j).push as[j] = as.extract (min i j) (j + 1)
    have h1 := @Array.push_extract_getElem _ nums 0 i if_pos
    -- h1 : (nums.extract 0 i).push nums[i] = nums.extract (min 0 i) (i + 1)
    simp only [Nat.zero_min] at h1
    -- h1 : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1)
    rw [← h1]
    have h2 : nums[i]! = nums[i] := by
      simp [Array.getElem!_eq_getD, Array.getD, if_pos]
    have h3 : nums[i] ≠ (2 : ℕ) := by
      intro heq
      have : nums[i]! = 2 := by rw [h2]; exact heq
      rw [if_pos_1] at this; exact absurd this (by decide)
    exact (Array.count_push_of_ne h3).symm

theorem goal_6
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = i)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    intros; expose_names; exact goal_3 nums i if_pos if_neg invariant_total_count

theorem goal_7
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg_1 : ¬nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    have h1 : (nums.extract 0 i).push nums[i] = nums.extract (min 0 i) (i + 1) :=
      Array.push_extract_getElem if_pos
    have h1' : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
      rw [h1]; simp [Nat.min_eq_left (Nat.zero_le i)]
    have hne : nums[i] ≠ 1 := by
      simp [Array.getElem!_eq_getD, Array.getD] at if_neg_1
      intro h
      apply if_neg_1
      simp [Array.getElem!_eq_getD, Array.getD, if_pos, h]
    have h2 : Array.count 1 ((nums.extract 0 i).push nums[i]) = Array.count 1 (nums.extract 0 i) :=
      Array.count_push_of_ne hne
    rw [← h1']
    exact h2.symm

theorem goal_8
    (nums : Array ℕ)
    (require_1 : ∀ i < nums.size, nums[i]! ≤ OfNat.ofNat 2)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (if_neg_1 : ¬nums[i]! = OfNat.ofNat 1)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = i)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) + OfNat.ofNat 1 = Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    -- First deduce nums[i]! = 2
    have h_le := require_1 i if_pos
    change nums[i]! ≤ 2 at h_le
    change ¬(nums[i]! = 0) at if_neg
    change ¬(nums[i]! = 1) at if_neg_1
    have h_val : nums[i]! = 2 := by omega
    -- extract 0 (i+1) = (extract 0 i).push nums[i]
    rw [Array.extract_succ_right (by omega : 0 < i + 1) if_pos]
    -- relate nums[i] to nums[i]!
    have h_getElem_eq : nums[i] = 2 := by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem if_pos] at h_val
      simpa using h_val
    rw [h_getElem_eq]
    rw [Array.count_push_self]

theorem goal_9
    (nums : Array ℕ)
    (i_4 : ℕ)
    (done_1 : nums.size ≤ i_4)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 0) nums := by
    have h : nums.extract 0 i_4 = nums := by
      rw [Array.extract_eq_self_iff]
      right
      exact ⟨rfl, done_1⟩
    rw [h]

theorem goal_10
    (nums : Array ℕ)
    (i_4 : ℕ)
    (done_1 : nums.size ≤ i_4)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 1) nums := by
    rw [Array.extract_eq_self_of_le done_1]

theorem goal_11
    (nums : Array ℕ)
    (i_4 : ℕ)
    (a_1 : i_4 ≤ nums.size)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = i_4)
    (done_1 : nums.size ≤ i_4)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 2) nums := by
    have h : i_4 = nums.size := Nat.le_antisymm a_1 done_1
    subst h
    rw [Array.extract_size]

theorem goal_12
    (nums : Array ℕ)
    (require_1 : ∀ i < nums.size, nums[i]! ≤ OfNat.ofNat 2)
    (i_4 : ℕ)
    (i_6 : ℕ)
    (res_1 : Array ℕ)
    (k : ℕ)
    (res_2 : Array ℕ)
    (a_5 : k ≤ nums.size)
    (invariant_res_size_2 : res_2.size = nums.size)
    (invariant_rest_zero_2 : ∀ (idx : ℕ), k ≤ idx → idx < nums.size → res_2[idx]! = OfNat.ofNat 0)
    (i_8 : ℕ)
    (res_3 : Array ℕ)
    (a_1 : i_4 ≤ nums.size)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = i_4)
    (invariant_zeros_final : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_2[idx]! = OfNat.ofNat 0)
    (fst_eq : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 0) nums)
    (fst_eq_1 : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 1) nums)
    (a_4 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ k)
    (invariant_ones_final : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums → res_2[idx]! = OfNat.ofNat 1)
    (invariant_twos_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ idx → idx < k → res_2[idx]! = OfNat.ofNat 2)
    (fst_eq_2 : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 2) nums)
    (invariant_count_sum : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size)
    (invariant_count_sum_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size)
    (a_2 : Array.count (OfNat.ofNat 0) nums ≤ i_6)
    (a_3 : i_6 ≤ Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums)
    (invariant_res_size_1 : res_1.size = nums.size)
    (invariant_zeros_intact : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_1[idx]! = OfNat.ofNat 0)
    (invariant_rest_zero_1 : ∀ (idx : ℕ), i_6 ≤ idx → idx < nums.size → res_1[idx]! = OfNat.ofNat 0)
    (invariant_ones_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < i_6 → res_1[idx]! = OfNat.ofNat 1)
    (done_3 : nums.size ≤ k)
    (i_9 : k = i_8 ∧ res_2 = res_3)
    (a : True)
    (done_1 : nums.size ≤ i_4)
    (invariant_c0_final_2 : True)
    (invariant_c1_final_2 : True)
    (invariant_c2_final_2 : True)
    (done_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ i_6)
    : postcondition nums res_3 := by
    sorry



theorem goal_12
    (nums : Array ℕ)
    (require_1 : ∀ i < nums.size, nums[i]! ≤ OfNat.ofNat 2)
    (i_4 : ℕ)
    (i_6 : ℕ)
    (res_1 : Array ℕ)
    (k : ℕ)
    (res_2 : Array ℕ)
    (a_5 : k ≤ nums.size)
    (invariant_res_size_2 : res_2.size = nums.size)
    (invariant_rest_zero_2 : ∀ (idx : ℕ), k ≤ idx → idx < nums.size → res_2[idx]! = OfNat.ofNat 0)
    (i_8 : ℕ)
    (res_3 : Array ℕ)
    (a_1 : i_4 ≤ nums.size)
    (invariant_total_count : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) + Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = i_4)
    (invariant_zeros_final : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_2[idx]! = OfNat.ofNat 0)
    (fst_eq : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 0) nums)
    (fst_eq_1 : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 1) nums)
    (a_4 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ k)
    (invariant_ones_final : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums → res_2[idx]! = OfNat.ofNat 1)
    (invariant_twos_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ idx → idx < k → res_2[idx]! = OfNat.ofNat 2)
    (fst_eq_2 : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i_4) = Array.count (OfNat.ofNat 2) nums)
    (invariant_count_sum : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size)
    (invariant_count_sum_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums + Array.count (OfNat.ofNat 2) nums = nums.size)
    (a_2 : Array.count (OfNat.ofNat 0) nums ≤ i_6)
    (a_3 : i_6 ≤ Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums)
    (invariant_res_size_1 : res_1.size = nums.size)
    (invariant_zeros_intact : ∀ idx < Array.count (OfNat.ofNat 0) nums, res_1[idx]! = OfNat.ofNat 0)
    (invariant_rest_zero_1 : ∀ (idx : ℕ), i_6 ≤ idx → idx < nums.size → res_1[idx]! = OfNat.ofNat 0)
    (invariant_ones_filled : ∀ (idx : ℕ), Array.count (OfNat.ofNat 0) nums ≤ idx → idx < i_6 → res_1[idx]! = OfNat.ofNat 1)
    (done_3 : nums.size ≤ k)
    (i_9 : k = i_8 ∧ res_2 = res_3)
    (a : True)
    (done_1 : nums.size ≤ i_4)
    (invariant_c0_final_2 : True)
    (invariant_c1_final_2 : True)
    (invariant_c2_final_2 : True)
    (done_2 : Array.count (OfNat.ofNat 0) nums + Array.count (OfNat.ofNat 1) nums ≤ i_6)
    : postcondition nums res_3 := by
    sorry



prove_correct SortColors by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i if_pos if_pos_1)
  exact (goal_1 nums i if_pos if_pos_1 invariant_total_count)
  exact (goal_2 nums i if_pos if_pos_1 invariant_total_count)
  exact (goal_3 nums i if_pos if_neg invariant_total_count)
  exact (goal_4 nums i if_pos if_pos_1)
  exact (goal_5 nums i if_pos if_pos_1)
  exact (goal_6 nums i if_pos if_neg invariant_total_count)
  exact (goal_7 nums i if_pos if_neg_1)
  exact (goal_8 nums require_1 i if_pos if_neg if_neg_1 invariant_total_count)
  exact (goal_9 nums i_4 done_1)
  exact (goal_10 nums i_4 done_1)
  exact (goal_11 nums i_4 a_1 invariant_total_count done_1)
  exact (goal_12 nums require_1 i_4 i_6 res_1 k res_2 a_5 invariant_res_size_2 invariant_rest_zero_2 i_8 res_3 a_1 invariant_total_count invariant_zeros_final fst_eq fst_eq_1 a_4 invariant_ones_final invariant_twos_filled fst_eq_2 invariant_count_sum invariant_count_sum_2 a_2 a_3 invariant_res_size_1 invariant_zeros_intact invariant_rest_zero_1 invariant_ones_filled done_3 i_9 a done_1 invariant_c0_final_2 invariant_c1_final_2 invariant_c2_final_2 done_2)
end Proof
