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
    674. Longest Continuous Increasing Subsequence: return the length of the longest strictly increasing contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A continuous subsequence is a contiguous subarray determined by a start index `l` and a positive length `len`.
    3. Such a subarray is strictly increasing when each adjacent pair increases: for all valid offsets `i`,
       nums[l+i] < nums[l+i+1].
    4. The output is the maximum length among all strictly increasing contiguous subarrays.
    5. Since a single element is trivially strictly increasing, when the array is non-empty the answer is at least 1.
-/

section Specs
-- A segment starting at `l` with length `len` is within bounds.
def segInBounds (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  l + len ≤ nums.size

-- A segment is required to be non-empty.
def segNonempty (len : Nat) : Prop :=
  1 ≤ len

-- Strictly increasing adjacent condition over a bounded, non-empty segment.
def segStrictlyIncreasing (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  segNonempty len ∧
  segInBounds nums l len ∧
  (∀ (i : Nat), i + 1 < len → nums[l + i]! < nums[l + i + 1]!)

-- Precondition: we follow the common problem constraint that the input array is non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- Postcondition: result is exactly the maximum length of any strictly increasing contiguous segment.
def postcondition (nums : Array Int) (result : Nat) : Prop :=
  result ≥ 1 ∧
  result ≤ nums.size ∧
  (∃ (l : Nat), segStrictlyIncreasing nums l result) ∧
  (∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len → len ≤ result)
end Specs

section Impl
method LongestContinuousIncreasingSubsequence (nums : Array Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
    -- O(n) time, O(1) extra space: single pass tracking current run length and best.
    let n := nums.size
    -- From precondition, n > 0, so answer is at least 1.
    let mut best : Nat := 1
    let mut curr : Nat := 1
    let mut i : Nat := 1

    while i < n
      -- i scans the array from 1 to n; at loop head we've processed indices < i.
      invariant "inv_i_bounds" (1 ≤ i ∧ i ≤ n)
      -- curr is the length of the strictly-increasing suffix ending at index i-1.
      invariant "inv_curr_range" (1 ≤ curr ∧ curr ≤ i)
      -- best is the maximum run length seen so far in the processed prefix [0,i).
      invariant "inv_best_range" (1 ≤ best ∧ best ≤ i)
      -- best is always at least the current suffix length.
      invariant "inv_best_ge_curr" (curr ≤ best)
      -- Witness: the current suffix [i-curr, i) is strictly increasing.
      invariant "inv_curr_segment" (segStrictlyIncreasing nums (i - curr) curr ∧ (i - curr) + curr = i)
      -- Maximality for segments ending at i-1: any increasing segment with end index i-1 has length ≤ curr.
      invariant "inv_curr_max_end" (∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len ∧ l + len = i → len ≤ curr)
      -- There exists a best-length increasing segment fully inside the processed prefix.
      invariant "inv_best_exists" (∃ l : Nat, segStrictlyIncreasing nums l best ∧ l + best ≤ i)
      -- best upper-bounds all increasing segments fully inside the processed prefix.
      invariant "inv_best_max" (∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len ∧ l + len ≤ i → len ≤ best)
      decreasing n - i
    do
      if nums[i - 1]! < nums[i]! then
        curr := curr + 1
      else
        curr := 1

      if best < curr then
        best := curr

      i := i + 1

    return best
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [1,3,5,4,7] => longest increasing contiguous subarray is [1,3,5], length 3
def test1_nums : Array Int := #[1, 3, 5, 4, 7]
def test1_Expected : Nat := 3

-- Test case 2: Example 2
-- nums = [2,2,2,2,2] => any strictly increasing contiguous subarray has length 1
def test2_nums : Array Int := #[2, 2, 2, 2, 2]
def test2_Expected : Nat := 1

-- Test case 3: Entire array strictly increasing
def test3_nums : Array Int := #[1, 2, 3, 4]
def test3_Expected : Nat := 4

-- Test case 4: Strictly decreasing array
def test4_nums : Array Int := #[4, 3, 2, 1]
def test4_Expected : Nat := 1

-- Test case 5: Single element
def test5_nums : Array Int := #[10]
def test5_Expected : Nat := 1

-- Test case 6: Includes negative numbers and increasing through zero
def test6_nums : Array Int := #[-3, -2, -1, 0]
def test6_Expected : Nat := 4

-- Test case 7: Increase, then drop, then longer increase
def test7_nums : Array Int := #[1, 3, 2, 4, 5]
def test7_Expected : Nat := 3

-- Test case 8: Equal adjacent elements break strict increase
def test8_nums : Array Int := #[1, 2, 2, 3]
def test8_Expected : Nat := 2

-- Test case 9: Multiple runs, longest at end
def test9_nums : Array Int := #[0, 1, 0, 1, 2, 3]
def test9_Expected : Nat := 4
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((LongestContinuousIncreasingSubsequence test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test LongestContinuousIncreasingSubsequence (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (curr : ℕ)
    (i : ℕ)
    (invariant_inv_curr_max_end : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i → len ≤ curr)
    : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i + OfNat.ofNat 1 → len ≤ curr + OfNat.ofNat 1 := by
  intro l len hlen hbound hinc hend
  -- Split on the length of the segment.
  cases len with
  | zero =>
      -- Contradiction: 1 ≤ 0.
      cases (Nat.not_succ_le_zero 0 (by simpa using hlen))
  | succ len' =>
      cases len' with
      | zero =>
          -- len = 1
          -- 1 ≤ curr + 1
          simpa using (Nat.succ_le_succ (Nat.zero_le curr))
      | succ len'' =>
          -- len = succ (succ len'')
          have hbound1 : l + Nat.succ len'' ≤ nums.size := by
            -- l + succ len'' ≤ l + succ (succ len'') ≤ nums.size
            have hle : l + Nat.succ len'' ≤ l + Nat.succ (Nat.succ len'') := by
              exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.le_succ len'')) l
            exact le_trans hle (by simpa using hbound)

          have hinc1 : ∀ i_1 : ℕ, i_1 + 1 < Nat.succ len'' → nums[l + i_1]! < nums[l + i_1 + 1]! := by
            intro i_1 hi_1
            have hi' : i_1 + 1 < Nat.succ (Nat.succ len'') := by
              exact lt_of_lt_of_le hi_1 (Nat.le_succ (Nat.succ len''))
            exact hinc i_1 (by simpa using hi')

          have hend1 : l + Nat.succ len'' = i := by
            have h' : (l + Nat.succ len'') + 1 = i + 1 := by
              -- rewrite l + succ (succ len'') as (l + succ len'') + 1
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hend
            exact Nat.add_right_cancel h'

          have hlen1 : (1 : ℕ) ≤ Nat.succ len'' :=
            Nat.succ_le_succ (Nat.zero_le len'')

          have hlen1_le_curr : Nat.succ len'' ≤ curr :=
            invariant_inv_curr_max_end l (Nat.succ len'') hlen1 hbound1 hinc1 hend1

          have hs : Nat.succ (Nat.succ len'') ≤ Nat.succ curr :=
            Nat.succ_le_succ hlen1_le_curr

          -- rewrite the RHS `curr + 1` as `Nat.succ curr`
          -- so the goal matches `hs` exactly.
          rw [← Nat.succ_eq_add_one curr]
          exact hs

theorem goal_1
    (nums : Array ℤ)
    (curr : ℕ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (a_6 : OfNat.ofNat 1 ≤ curr ∧ i - curr + curr ≤ nums.size ∧ ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < curr → nums[i - curr + i_1]! < nums[i - curr + i_1 + OfNat.ofNat 1]!)
    (a_7 : i - curr + curr = i)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i - OfNat.ofNat 1]! < nums[i]!)
    : ∃ l, (l + (curr + OfNat.ofNat 1) ≤ nums.size ∧ ∀ i < curr, nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) ∧ l + (curr + OfNat.ofNat 1) ≤ i + OfNat.ofNat 1 := by
  refine ⟨i - curr, ?_⟩
  constructor
  · constructor
    · -- in-bounds
      have hi1 : i + 1 ≤ nums.size := Nat.succ_le_of_lt if_pos
      have hEq : (i - curr) + (curr + 1) = i + 1 := by
        calc
          (i - curr) + (curr + 1) = (i - curr + curr) + 1 := by
            simpa [Nat.add_assoc] using (Nat.add_assoc (i - curr) curr 1).symm
          _ = i + 1 := by simpa [a_7]
      simpa [hEq] using hi1
    · -- strict adjacent increases for indices < curr
      intro j hj
      have hjle : j + 1 ≤ curr := Nat.succ_le_of_lt hj
      cases lt_or_eq_of_le hjle with
      | inl hlt =>
          -- inside the old curr-segment
          simpa [Nat.add_assoc] using (a_6.2.2 j hlt)
      | inr heq =>
          -- last edge: use if_pos_1
          have hj1 : (i - curr) + j + 1 = i := by
            calc
              (i - curr) + j + 1 = (i - curr) + (j + 1) := by simp [Nat.add_assoc]
              _ = (i - curr) + curr := by simpa [heq]
              _ = i := by simpa [Nat.add_assoc] using a_7
          have hj0 : (i - curr) + j = i - 1 := by
            have h := congrArg (fun t : Nat => t - 1) hj1
            simpa [Nat.add_assoc] using h
          -- rewrite indices to i-1 and i
          simpa [hj0, hj1, Nat.sub_add_cancel a] using if_pos_1
  · -- end index bound (indeed equality)
    have hEq : (i - curr) + (curr + 1) = i + 1 := by
      calc
        (i - curr) + (curr + 1) = (i - curr + curr) + 1 := by
          simpa [Nat.add_assoc] using (Nat.add_assoc (i - curr) curr 1).symm
        _ = i + 1 := by simpa [a_7]
    simpa [hEq]

theorem goal_2
    (nums : Array ℤ)
    (best : ℕ)
    (curr : ℕ)
    (i : ℕ)
    (if_pos_2 : best < curr + OfNat.ofNat 1)
    (invariant_inv_curr_max_end : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i → len ≤ curr)
    (invariant_inv_best_max : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len ≤ i → len ≤ best)
    : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len ≤ i + OfNat.ofNat 1 → len ≤ curr + OfNat.ofNat 1 := by
  intro l len hlen hbounds hincr hle
  by_cases hEq : l + len = i + 1
  · exact goal_0 nums curr i invariant_inv_curr_max_end l len hlen hbounds hincr hEq
  · have hlt : l + len < i + 1 := lt_of_le_of_ne hle hEq
    have hlt' : l + len < Nat.succ i := lt_of_lt_of_eq hlt (Nat.add_one i)
    have hle_i : l + len ≤ i := (Nat.lt_succ_iff.mp hlt')
    have hlen_best : len ≤ best :=
      invariant_inv_best_max l len hlen hbounds hincr hle_i
    have hbest_lt_succ : best < Nat.succ curr := lt_of_lt_of_eq if_pos_2 (Nat.add_one curr)
    have best_le_curr : best ≤ curr := Nat.lt_succ_iff.mp hbest_lt_succ
    have hlen_curr : len ≤ curr := le_trans hlen_best best_le_curr
    have hc : curr ≤ curr + 1 := by
      calc
        curr ≤ Nat.succ curr := Nat.le_succ curr
        _ = curr + 1 := (Nat.add_one curr).symm
    exact le_trans hlen_curr hc

theorem goal_3
    (nums : Array ℤ)
    (curr : ℕ)
    (i : ℕ)
    (invariant_inv_curr_max_end : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i → len ≤ curr)
    : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i + OfNat.ofNat 1 → len ≤ curr + OfNat.ofNat 1 := by
    intros; expose_names; exact goal_0 nums curr i invariant_inv_curr_max_end l len h h_1 h_2 h_3

theorem goal_4
    (nums : Array ℤ)
    (best : ℕ)
    (curr : ℕ)
    (i : ℕ)
    (invariant_inv_curr_max_end : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i → len ≤ curr)
    (invariant_inv_best_max : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len ≤ i → len ≤ best)
    (if_neg : curr + OfNat.ofNat 1 ≤ best)
    : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len ≤ i + OfNat.ofNat 1 → len ≤ best := by
    intro l len hlen hsize hinc hprefix
    have hprefix' : l + len ≤ i + 1 := by
      simpa using hprefix
    by_cases hleI : l + len ≤ i
    · exact invariant_inv_best_max l len hlen hsize hinc hleI
    · have hi_lt : i < l + len := Nat.lt_of_not_ge hleI
      have hsuc_le : i + 1 ≤ l + len := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hi_lt)
      have heq : l + len = i + 1 := Nat.le_antisymm hprefix' hsuc_le
      have hlen_le_curr : len ≤ curr + 1 := by
        -- any increasing segment ending at i+1 has length ≤ curr+1
        simpa using
          (goal_3 nums curr i invariant_inv_curr_max_end l len hlen hsize hinc (by simpa using heq))
      exact le_trans hlen_le_curr (by simpa using if_neg)

theorem goal_5
    (nums : Array ℤ)
    (best : ℕ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (invariant_inv_best_exists : ∃ l, (OfNat.ofNat 1 ≤ best ∧ l + best ≤ nums.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < best → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) ∧ l + best ≤ i)
    (if_neg : nums[i]! ≤ nums[i - OfNat.ofNat 1]!)
    : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len = i + OfNat.ofNat 1 → len ≤ OfNat.ofNat 1 := by
  intro l len hlen hbound hinc hend
  cases len with
  | zero =>
      simp
  | succ len1 =>
      cases len1 with
      | zero =>
          simp
      | succ k =>
          -- Turn `l + (k+2) = i+1` into `succ (succ (l+k)) = succ i`.
          have hend3 : Nat.succ (Nat.succ (l + k)) = Nat.succ i := by
            have h := hend
            -- rewrite `i + 1` as `succ i`
            rw [Nat.add_one] at h
            -- rewrite the left-hand side twice using `Nat.add_succ`
            rw [Nat.add_succ] at h
            rw [Nat.add_succ] at h
            -- now both sides are succ-forms
            exact h
          have hi : Nat.succ (l + k) = i := by
            exact Nat.succ.inj hend3
          have hk0 : l + k = i - 1 := by
            have : i = Nat.succ (l + k) := hi.symm
            -- rewrite `i` and simplify
            rw [this]
            simp
          have hlast : nums[l + k]! < nums[l + k + 1]! := by
            have hklt : k + 1 < Nat.succ (Nat.succ k) := by omega
            simpa using hinc k hklt
          have hlast' : nums[i - 1]! < nums[i]! := by
            have htmp : nums[i - 1]! < nums[i - 1 + 1]! := by
              simpa [hk0, Nat.add_assoc] using hlast
            simpa [Nat.sub_add_cancel a] using htmp
          have : False := by
            have : nums[i - 1]! < nums[i - 1]! := lt_of_lt_of_le hlast' if_neg
            exact lt_irrefl _ this
          exact False.elim this

theorem goal_6
    (nums : Array ℤ)
    (best : ℕ)
    (i : ℕ)
    (a : OfNat.ofNat 1 ≤ i)
    (a_4 : OfNat.ofNat 1 ≤ best)
    (invariant_inv_best_exists : ∃ l, (OfNat.ofNat 1 ≤ best ∧ l + best ≤ nums.size ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < best → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) ∧ l + best ≤ i)
    (invariant_inv_best_max : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len ≤ i → len ≤ best)
    (if_neg : nums[i]! ≤ nums[i - OfNat.ofNat 1]!)
    : ∀ (l len : ℕ), OfNat.ofNat 1 ≤ len → l + len ≤ nums.size → (∀ (i : ℕ), i + OfNat.ofNat 1 < len → nums[l + i]! < nums[l + i + OfNat.ofNat 1]!) → l + len ≤ i + OfNat.ofNat 1 → len ≤ best := by
  intro l len hlen hsz hinc hle
  have hlt_or_eq : l + len < i + 1 ∨ l + len = i + 1 := by
    exact Nat.lt_or_eq_of_le hle
  cases hlt_or_eq with
  | inl hlt =>
      have hlt_succ : l + len < Nat.succ i :=
        lt_of_lt_of_eq hlt (Nat.add_one i)
      have hle' : l + len ≤ i := (Nat.lt_succ_iff.mp hlt_succ)
      exact invariant_inv_best_max l len hlen hsz hinc hle'
  | inr heq =>
      have hlen_le1 : len ≤ 1 := by
        exact goal_5 nums best i a invariant_inv_best_exists if_neg l len hlen hsz hinc heq
      exact Nat.le_trans hlen_le1 a_4


prove_correct LongestContinuousIncreasingSubsequence by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums curr i invariant_inv_curr_max_end)
  exact (goal_1 nums curr i a a_6 a_7 if_pos if_pos_1)
  exact (goal_2 nums best curr i if_pos_2 invariant_inv_curr_max_end invariant_inv_best_max)
  exact (goal_3 nums curr i invariant_inv_curr_max_end)
  exact (goal_4 nums best curr i invariant_inv_curr_max_end invariant_inv_best_max if_neg)
  exact (goal_5 nums best i a invariant_inv_best_exists if_neg)
  exact (goal_6 nums best i a a_4 invariant_inv_best_exists invariant_inv_best_max if_neg)
end Proof
