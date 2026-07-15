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
    918. Maximum Sum Circular Subarray: compute the maximum possible sum of a non-empty subarray of a circular integer array.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an integer array `nums` with length `n`.
    2. A circular subarray is determined by a start index `start` and a length `len`.
    3. The chosen elements are `nums[start], nums[(start+1) mod n], ..., nums[(start+len-1) mod n]`.
    4. The subarray must be non-empty, so `1 ≤ len`.
    5. The subarray may use each element of the underlying fixed buffer at most once, so `len ≤ n`.
    6. The output is the maximum possible sum among all valid circular subarrays.
    7. The result must be achievable by at least one valid circular subarray and must be greater than or equal to
       the sum of every valid circular subarray.
-/

section Specs
-- Helper function: sum of a circular segment of length `len`, starting at index `start`.
-- Implemented as a finite sum over indices `0 .. len-1`.
-- When `arr.size > 0`, each index `(start + i) % arr.size` is within bounds.
def circSegmentSum (arr : Array Int) (start : Nat) (len : Nat) : Int :=
  (Finset.range len).sum (fun i => arr[(start + i) % arr.size]!)

-- A (start,len) pair is valid if it picks a non-empty circular segment of length at most `n`.
def isValidCircSegment (arr : Array Int) (start : Nat) (len : Nat) : Prop :=
  arr.size > 0 ∧ start < arr.size ∧ 1 ≤ len ∧ len ≤ arr.size

-- Precondition: array must be non-empty (subarray is required to be non-empty).
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- Postcondition: `result` is the maximum circular subarray sum.
-- 1) Achievability: some valid circular segment sums exactly to `result`.
-- 2) Maximality: every valid circular segment has sum ≤ result.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (len : Nat),
      isValidCircSegment nums start len ∧ circSegmentSum nums start len = result) ∧
  (∀ (start : Nat) (len : Nat),
      isValidCircSegment nums start len → circSegmentSum nums start len ≤ result)
end Specs

section Impl
method MaxSumCircularSubarray (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Kadane's algorithm variant for circular arrays (O(n) time, O(1) extra space)
  let n := nums.size
  let mut i : Nat := 0
  let mut total : Int := 0

  -- Track maximum subarray sum (non-empty)
  let mut curMax : Int := nums[0]!
  let mut maxSum : Int := nums[0]!

  -- Track minimum subarray sum (non-empty)
  let mut curMin : Int := nums[0]!
  let mut minSum : Int := nums[0]!

  while i < n
    invariant "inv_n" n = nums.size
    invariant "inv_i_le_n" i ≤ n
    invariant "inv_total_prefix" total = (Finset.range i).sum (fun j => nums[j]!)
    invariant "inv_curMax_spec" (i = 0) ∨
      ((∃ start, start < i ∧ (Finset.range (i - start)).sum (fun k => nums[start + k]!) = curMax) ∧
       (∀ start, start < i → (Finset.range (i - start)).sum (fun k => nums[start + k]!) ≤ curMax))
    invariant "inv_curMin_spec" (i = 0) ∨
      ((∃ start, start < i ∧ (Finset.range (i - start)).sum (fun k => nums[start + k]!) = curMin) ∧
       (∀ start, start < i → curMin ≤ (Finset.range (i - start)).sum (fun k => nums[start + k]!)))
    invariant "inv_maxSum_spec" (i = 0) ∨
      ((∃ start len, start < i ∧ 1 ≤ len ∧ start + len ≤ i ∧
          (Finset.range len).sum (fun k => nums[start + k]!) = maxSum) ∧
       (∀ start len, start < i ∧ 1 ≤ len ∧ start + len ≤ i →
          (Finset.range len).sum (fun k => nums[start + k]!) ≤ maxSum))
    invariant "inv_minSum_spec" (i = 0) ∨
      ((∃ start len, start < i ∧ 1 ≤ len ∧ start + len ≤ i ∧
          (Finset.range len).sum (fun k => nums[start + k]!) = minSum) ∧
       (∀ start len, start < i ∧ 1 ≤ len ∧ start + len ≤ i →
          minSum ≤ (Finset.range len).sum (fun k => nums[start + k]!)))
    invariant "inv_max_ge_curMax" maxSum ≥ curMax
    invariant "inv_min_le_curMin" minSum ≤ curMin
    decreasing n - i
  do
    let x := nums[i]!
    if i = 0 then
      -- initialize from first element
      total := x
      curMax := x
      maxSum := x
      curMin := x
      minSum := x
    else
      total := total + x
      -- max ending here
      if curMax + x < x then
        curMax := x
      else
        curMax := curMax + x
      if maxSum < curMax then
        maxSum := curMax

      -- min ending here
      if curMin + x > x then
        curMin := x
      else
        curMin := curMin + x
      if minSum > curMin then
        minSum := curMin
    i := i + 1

  -- If all numbers are negative, maxSum is the answer (wrapping would pick empty complement)
  if maxSum < 0 then
    return maxSum
  else
    let wrap := total - minSum
    if wrap > maxSum then
      return wrap
    else
      return maxSum
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: nums = [1,-2,3,-2]
-- Output: 3
-- Explanation: Subarray [3] has maximum sum 3.
def test1_nums : Array Int := #[1, -2, 3, -2]
def test1_Expected : Int := 3

-- Test case 2: Example 2 (wrap-around optimal)
def test2_nums : Array Int := #[5, -3, 5]
def test2_Expected : Int := 10

-- Test case 3: Example 3 (all negative)
def test3_nums : Array Int := #[-3, -2, -3]
def test3_Expected : Int := -2

-- Test case 4: Single element (must choose that element)
def test4_nums : Array Int := #[7]
def test4_Expected : Int := 7

-- Test case 5: All positive (best is whole array)
def test5_nums : Array Int := #[2, 3, 1]
def test5_Expected : Int := 6

-- Test case 6: Wrap-around beats any linear segment
-- Best is taking last and first element: 8 + 8 = 16
def test6_nums : Array Int := #[8, -1, -3, 8]
def test6_Expected : Int := 16

-- Test case 7: Contains zeros; best sum can be 0 even with negatives present
-- E.g., choose subarray [0]
def test7_nums : Array Int := #[0, -5, 0]
def test7_Expected : Int := 0

-- Test case 8: Two elements (smallest non-trivial size)
def test8_nums : Array Int := #[-1, 2]
def test8_Expected : Int := 2

-- Test case 9: Multiple candidates; maximum is achieved by a non-wrapping segment
-- Best is [3, -1, 2] with sum 4
def test9_nums : Array Int := #[3, -1, 2, -1]
def test9_Expected : Int := 4

-- Recommend to validate: all-negative arrays, wrap-around-optimal cases, single-element arrays
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MaxSumCircularSubarray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MaxSumCircularSubarray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MaxSumCircularSubarray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MaxSumCircularSubarray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MaxSumCircularSubarray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MaxSumCircularSubarray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MaxSumCircularSubarray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MaxSumCircularSubarray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MaxSumCircularSubarray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MaxSumCircularSubarray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    : (∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ x ≤ OfNat.ofNat 1 ∧ ∑ x ∈ Finset.range x, nums[x]! = nums[OfNat.ofNat 0]!) ∧ ∀ (start len : ℕ), start = OfNat.ofNat 0 → OfNat.ofNat 1 ≤ len → start + len ≤ OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ nums[OfNat.ofNat 0]! := by
  constructor
  · refine ⟨1, by decide, by decide, ?_⟩
    simp
  · intro start len hstart hlen hbound
    subst hstart
    have hle : len ≤ 1 := by
      simpa using hbound
    have hEq : len = 1 := Nat.le_antisymm hle hlen
    subst hEq
    simp

theorem goal_1
    (nums : Array ℤ)
    : (∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ x ≤ OfNat.ofNat 1 ∧ ∑ x ∈ Finset.range x, nums[x]! = nums[OfNat.ofNat 0]!) ∧ ∀ (start len : ℕ), start = OfNat.ofNat 0 → OfNat.ofNat 1 ≤ len → start + len ≤ OfNat.ofNat 1 → nums[OfNat.ofNat 0]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
  constructor
  · refine ⟨1, by decide, by decide, ?_⟩
    simp
  · intro start len hstart hlen hbound
    subst hstart
    have hlenle : len ≤ 1 := by
      simpa using hbound
    have hlen1 : len = 1 := Nat.le_antisymm hlenle hlen
    subst hlen1
    simp

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    intros; expose_names; exact Eq.symm (Finset.sum_range_succ (getElem! nums) i)

theorem goal_3
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_2 : maxSum < nums[i]!)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    (if_pos_3 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ nums[i]! := by
  classical
  -- extract the useful half of the curMax invariant (since i ≠ 0)
  have hcurMaxSpec : (∃ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) = curMax) ∧
      ∀ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ curMax := by
    rcases invariant_inv_curMax_spec with hi0 | h
    · exfalso
      exact if_neg hi0
    · exact h

  constructor
  · -- witness start = i, segment length 1
    refine ⟨i, Nat.lt_succ_self i, ?_⟩
    simp
  · intro start hstart
    have hle : start ≤ i := Nat.le_of_lt_succ hstart
    -- split start < i or start = i
    rcases lt_or_eq_of_le hle with hlt | rfl
    · -- case start < i
      set S : ℤ := ∑ k ∈ Finset.range (i - start), nums[start + k]! with hSdef
      have hSle : S ≤ curMax := by
        -- from invariant upper bound
        simpa [S, hSdef] using (hcurMaxSpec.2 start hlt)
      have hSlt0 : S < (0 : ℤ) := lt_of_le_of_lt hSle (by simpa using if_pos_1)

      -- split off the last term of the sum of length (i+1-start)
      have hlen : i + 1 - start = Nat.succ (i - start) := by
        have : Nat.succ i - start = Nat.succ (i - start) := Nat.succ_sub (m := i) (n := start) hle
        simpa [Nat.succ_eq_add_one] using this

      have hsum : (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!) = S + nums[i]! := by
        have hi : start + (i - start) = i := Nat.add_sub_of_le hle
        calc
          (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!)
              = (∑ k ∈ Finset.range (Nat.succ (i - start)), nums[start + k]!) := by
                  simp [hlen]
          _ = nums[start + (i - start)]! + (∑ k ∈ Finset.range (i - start), nums[start + k]!) := by
                  simp [Finset.range_succ, Nat.succ_eq_add_one]
          _ = S + nums[i]! := by
                  simp [S, hSdef, hi, add_comm, add_left_comm, add_assoc]

      have : (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!) < nums[i]! := by
        simpa [hsum] using (add_lt_add_right hSlt0 (nums[i]!))
      exact le_of_lt this

    · -- case start = i
      simp

theorem goal_4
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_1 : curMin ≤ OfNat.ofNat 0)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
  have hi0 : i ≠ 0 := by
    simpa using if_neg

  have hspec : (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧
      ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]! := by
    rcases invariant_inv_curMin_spec with h0 | h
    · exfalso
      exact hi0 (by simpa using h0)
    · exact h

  rcases hspec with ⟨hex, hminOld⟩
  rcases hex with ⟨start0, hstart0lt, hstart0sum⟩

  constructor
  · refine ⟨start0, ?_, ?_⟩
    · exact lt_trans hstart0lt (Nat.lt_succ_self i)
    · have hlen : i + 1 - start0 = (i - start0).succ := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.succ_sub (m := i) (n := start0) (Nat.le_of_lt hstart0lt))
      calc
        (∑ k ∈ Finset.range (i + 1 - start0), nums[start0 + k]!)
            = (∑ k ∈ Finset.range ((i - start0).succ), nums[start0 + k]!) := by
                simpa [hlen]
        _ = nums[start0 + (i - start0)]! + (∑ k ∈ Finset.range (i - start0), nums[start0 + k]!) := by
              simp [Finset.range_succ, add_assoc, add_comm, add_left_comm]
        _ = (∑ k ∈ Finset.range (i - start0), nums[start0 + k]!) + nums[i]! := by
              have hidx : start0 + (i - start0) = i :=
                Nat.add_sub_cancel' (Nat.le_of_lt hstart0lt)
              simp [hidx, add_assoc, add_comm, add_left_comm]
        _ = curMin + nums[i]! := by
              simp [hstart0sum, add_assoc, add_comm, add_left_comm]

  · intro start hstartlt
    have hstartle : start ≤ i :=
      Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hstartlt)
    cases Nat.lt_or_eq_of_le hstartle with
    | inl hlt =>
        have hold : curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]! :=
          hminOld start hlt
        have hold' : curMin + nums[i]! ≤ (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! :=
          add_le_add_right hold (nums[i]!)
        have hlen : i + 1 - start = (i - start).succ := by
          simpa [Nat.succ_eq_add_one] using
            (Nat.succ_sub (m := i) (n := start) (Nat.le_of_lt hlt))
        have hsum : (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!) =
            (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
          have hidx : start + (i - start) = i := Nat.add_sub_cancel' (Nat.le_of_lt hlt)
          calc
            (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!)
                = (∑ k ∈ Finset.range ((i - start).succ), nums[start + k]!) := by
                    simpa [hlen]
            _ = nums[start + (i - start)]! + (∑ k ∈ Finset.range (i - start), nums[start + k]!) := by
                    simp [Finset.range_succ, add_assoc, add_comm, add_left_comm]
            _ = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
                    simp [hidx, add_assoc, add_comm, add_left_comm]
        simpa [hsum] using hold'

    | inr heq =>
        have hle : curMin + nums[i]! ≤ nums[i]! := by
          have h := add_le_add_right if_neg_1 (nums[i]!)
          simpa [add_assoc, add_comm, add_left_comm] using h
        -- rewrite the goal using start = i and simplify the range sum
        simpa [heq, Nat.succ_eq_add_one] using
          (show curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + 1 - i), nums[i + k]! from by
            simpa using hle)

theorem goal_5
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_2 : maxSum < nums[i]!)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    (if_pos_3 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ nums[i]! := by
  constructor
  · refine ⟨i, ?_, 1, ?_, ?_, ?_⟩
    · simpa using Nat.lt_succ_self i
    · simp
    · simp
    · simp
  · intro start len hstart hlen hle
    -- bring in the specialized suffix bound from goal_3
    have hgoal3 :
        (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧
          ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ nums[i]! := by
      simpa using
        (goal_3 (nums := nums) (curMax := curMax) (curMin := curMin) (i := i) (maxSum := maxSum)
          (minSum := minSum) (invariant_inv_i_le_n := invariant_inv_i_le_n)
          (invariant_inv_curMax_spec := invariant_inv_curMax_spec)
          (invariant_inv_curMin_spec := invariant_inv_curMin_spec)
          (invariant_inv_maxSum_spec := invariant_inv_maxSum_spec)
          (invariant_inv_minSum_spec := invariant_inv_minSum_spec) (if_pos := if_pos) (if_neg := if_neg)
          (if_pos_2 := if_pos_2) (if_pos_1 := if_pos_1) (if_pos_3 := if_pos_3))

    have hle' : start + len ≤ Nat.succ i := by
      simpa [Nat.succ_eq_add_one, add_assoc] using hle

    rcases Nat.le_or_eq_of_le_succ hle' with hle_i | hEq
    · -- subarray entirely within the first i elements
      have hmax_univ :
          ∀ (s l : ℕ), s < i → (1 : ℕ) ≤ l → s + l ≤ i →
            ∑ k ∈ Finset.range l, nums[s + k]! ≤ maxSum := by
        rcases invariant_inv_maxSum_spec with hi0 | hspec
        · exfalso; exact if_neg hi0
        · exact hspec.2

      have hstart_i : start < i := by
        have hstart1_le : start + 1 ≤ start + len := Nat.add_le_add_left hlen start
        have hstart1_le_i : start + 1 ≤ i := le_trans hstart1_le hle_i
        exact lt_of_lt_of_le (Nat.lt_succ_self start) hstart1_le_i

      exact le_trans (hmax_univ start len hstart_i hlen hle_i) (le_of_lt if_pos_2)
    · -- subarray ends exactly at i
      have hlenEq : len = i.succ - start := by
        -- hEq : start + len = i.succ
        exact Nat.eq_sub_of_add_eq' hEq

      have hseg_le :
          ∑ k ∈ Finset.range (i.succ - start), nums[start + k]! ≤ nums[i]! := by
        have hstart' : start < i + 1 := by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using hstart
        simpa [Nat.succ_eq_add_one, add_assoc] using (hgoal3.2 start hstart')

      simpa [hlenEq] using hseg_le

theorem goal_6
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (minSum : ℤ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_1 : curMin ≤ OfNat.ofNat 0)
    (if_pos_3 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMin + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → curMin + nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
  -- Use the already-proved fact about the new "curMin + nums[i]!" value for segments ending at `i`.
  have h4 := goal_4 nums curMin i invariant_inv_curMin_spec if_neg if_neg_1
  rcases h4 with ⟨h4_exists, h4_lower⟩

  constructor
  · -- existence: take the segment ending at `i` from goal_4 and package it with an explicit length
    rcases h4_exists with ⟨start, hstart, hsum⟩
    refine ⟨start, hstart, (i + 1 - start), ?_, ?_, ?_⟩
    · -- nonempty length
      have hxpos : 0 < i + 1 - start := Nat.sub_pos_of_lt (by simpa using hstart)
      -- `1 ≤ x` ↔ `0 < x`
      exact (Nat.succ_le_iff).2 (by simpa using hxpos)
    · -- segment is within bounds
      exact le_of_eq (Nat.add_sub_of_le (Nat.le_of_lt (by simpa using hstart)))
    · -- sum equality
      simpa using hsum

  · -- minimality: any segment in the prefix `i+1` has sum ≥ `curMin + nums[i]!`
    intro start len hstart hlen hend
    have h_cases : start + len < i + 1 ∨ start + len = i + 1 := lt_or_eq_of_le (by simpa using hend)
    cases h_cases with
    | inl hlt =>
        -- segment is fully contained in the old prefix `i`
        have hend' : start + len ≤ i := (Nat.lt_succ_iff).1 (by simpa using hlt)
        have h0len : 0 < len := (Nat.succ_le_iff).1 (by simpa using hlen)
        have hstartlt : start < start + len := by
          simpa [Nat.zero_add] using (Nat.add_lt_add_left h0len start)
        have hstart_i : start < i := lt_of_lt_of_le hstartlt hend'

        -- old minSum lower bound for segments inside `i`
        have hminLower : minSum ≤ (∑ k ∈ Finset.range len, nums[start + k]!) := by
          rcases invariant_inv_minSum_spec with hi0 | hspec
          · exfalso; exact if_neg hi0
          · exact hspec.2 start len hstart_i hlen hend'

        -- chain using `curMin + nums[i]! < minSum`
        exact le_trans (le_of_lt if_pos_3) hminLower

    | inr heq =>
        -- segment ends at `i` (i.e. `start + len = i+1`), so use goal_4's bound
        have hlenEq : len = i + 1 - start := Nat.eq_sub_of_add_eq' (by simpa using heq)
        have h := h4_lower start hstart
        -- rewrite the length
        simpa [hlenEq.symm] using h

theorem goal_7
    (nums : Array ℤ)
    (i : ℕ)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    intros; expose_names; exact goal_2 nums i

theorem goal_8
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_2 : maxSum < nums[i]!)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    (if_neg_2 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ nums[i]! := by
  constructor
  · refine ⟨i, Nat.lt_succ_self i, ?_⟩
    simp
  · intro start hstart
    by_cases hsi : start = i
    · subst hsi
      simp
    · have hle : start ≤ i := Nat.le_of_lt_succ hstart
      have hlt : start < i := lt_of_le_of_ne hle hsi

      have hcur : (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧
            ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax := by
        cases invariant_inv_curMax_spec with
        | inl hi0 => exact False.elim (if_neg hi0)
        | inr h => exact h

      have hbound : ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax :=
        hcur.2 start hlt

      have hrewrite :
          (∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]!) =
            (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
        classical
        have hlen0 : Nat.succ i - start = Nat.succ (i - start) := (Nat.succ_sub (m := i) (n := start) hle)
        have hlen : i + OfNat.ofNat 1 - start = Nat.succ (i - start) := by
          simpa [Nat.succ_eq_add_one] using hlen0
        have hadd : start + (i - start) = i := Nat.add_sub_of_le hle
        calc
          (∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]!)
              = ∑ k ∈ Finset.range (Nat.succ (i - start)), nums[start + k]! := by
                  simpa [hlen]
          _ = nums[start + (i - start)]! + (∑ k ∈ Finset.range (i - start), nums[start + k]!) := by
                  simp [Finset.range_succ, Finset.sum_insert, Finset.not_mem_range_self, add_comm,
                    add_left_comm, add_assoc]
          _ = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
                  simpa [hadd, add_comm, add_left_comm, add_assoc]

      have hstep :
          (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! ≤ curMax + nums[i]! :=
        add_le_add_right hbound (nums[i]!)

      have hcur0 : curMax + nums[i]! ≤ nums[i]! := by
        have : curMax + nums[i]! < (0 : ℤ) + nums[i]! := add_lt_add_right if_pos_1 (nums[i]!)
        exact le_of_lt (by simpa using this)

      calc
        (∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]!)
            = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
                simpa using hrewrite
        _ ≤ curMax + nums[i]! := hstep
        _ ≤ nums[i]! := hcur0

theorem goal_9
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_1 : curMin ≤ OfNat.ofNat 0)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    intros; expose_names; exact goal_4 nums curMin i invariant_inv_curMin_spec if_neg if_neg_1

theorem goal_10
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_2 : maxSum < nums[i]!)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    (if_neg_2 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ nums[i]! := by
  have hmax_all : ∀ (start len : ℕ), start < i → 1 ≤ len → start + len ≤ i →
      (∑ k ∈ Finset.range len, nums[start + k]!) ≤ maxSum := by
    rcases invariant_inv_maxSum_spec with hi0 | hspec
    · exfalso; exact if_neg hi0
    · exact hspec.2

  have hcur_all : ∀ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ curMax := by
    rcases invariant_inv_curMax_spec with hi0 | hspec
    · exfalso; exact if_neg hi0
    · exact hspec.2

  constructor
  · refine ⟨i, ?_, 1, ?_, ?_, ?_⟩
    · simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_self i)
    · simp
    · simp
    · simp

  · intro start len hstart hlen hle
    by_cases hleI : start + len ≤ i
    · -- segment entirely in old prefix
      have hs : start < i := by
        have h1 : start + 1 ≤ start + len := Nat.add_le_add_left hlen start
        have h2 : start + 1 ≤ i := le_trans h1 hleI
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self start) (by simpa [Nat.succ_eq_add_one] using h2)
      have hsum_le : (∑ k ∈ Finset.range len, nums[start + k]!) ≤ maxSum :=
        hmax_all start len hs hlen hleI
      exact le_trans hsum_le (le_of_lt if_pos_2)

    · -- segment must end exactly at i
      have hEq : start + len = i + 1 := by
        have h' : start + len ≤ i ∨ start + len = i + 1 :=
          Nat.le_or_eq_of_le_succ (by simpa [Nat.succ_eq_add_one] using hle)
        cases h' with
        | inl hle' => exact (False.elim (hleI hle'))
        | inr hEq' => exact hEq'

      cases len with
      | zero =>
          exfalso
          exact (Nat.not_succ_le_zero 0) (by simpa [Nat.succ_eq_add_one] using hlen)
      | succ l =>
          -- special case start = i, so len = 1
          by_cases hstartEq : start = i
          · subst hstartEq
            have hl : l = 0 := by
              have h' : start + Nat.succ l = start + 1 := by
                simpa [Nat.succ_eq_add_one] using hEq
              exact Nat.succ.inj (Nat.add_left_cancel h')
            subst hl
            simp

          · -- main case start < i
            have hs : start < i := by
              have hsle : start ≤ i := Nat.le_of_lt_succ (by
                simpa [Nat.succ_eq_add_one] using hstart)
              exact lt_of_le_of_ne hsle hstartEq

            have hEq' : start + l = i := by
              -- rewrite hEq as succ equality and cancel succ
              have htemp : Nat.succ (start + l) = i + 1 := by
                have htemp := hEq
                rw [Nat.add_succ] at htemp
                exact htemp
              have htemp' := htemp
              rw [← Nat.succ_eq_add_one] at htemp'
              exact Nat.succ.inj htemp'

            have hil : i - start = l := by
              simpa [hEq'] using (Nat.add_sub_cancel_left start l)

            have hpart_le : (∑ k ∈ Finset.range l, nums[start + k]!) ≤ curMax := by
              simpa [hil] using hcur_all start hs

            have hpart_lt0 : (∑ k ∈ Finset.range l, nums[start + k]!) < 0 :=
              lt_of_le_of_lt hpart_le if_pos_1

            have hsum_le' : nums[i]! + (∑ k ∈ Finset.range l, nums[start + k]!) ≤ nums[i]! := by
              have hlt : nums[i]! + (∑ k ∈ Finset.range l, nums[start + k]!) < nums[i]! + 0 :=
                add_lt_add_left hpart_lt0 (nums[i]!)
              simpa using (le_of_lt hlt)

            have hsum_eq : (∑ k ∈ Finset.range (Nat.succ l), nums[start + k]!) =
                nums[i]! + (∑ k ∈ Finset.range l, nums[start + k]!) := by
              calc
                (∑ k ∈ Finset.range (Nat.succ l), nums[start + k]!)
                    = nums[start + l]! + (∑ k ∈ Finset.range l, nums[start + k]!) := by
                        simp [Finset.range_succ, Finset.not_mem_range_self, Nat.add_assoc]
                _ = nums[i]! + (∑ k ∈ Finset.range l, nums[start + k]!) := by
                        simp [hEq', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

            simpa [hsum_eq] using hsum_le'

theorem goal_11
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (minSum : ℤ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_1 : curMin ≤ OfNat.ofNat 0)
    (if_neg_2 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
  classical
  -- extract the nontrivial part of the minSum invariant at `i`
  have hMinSpec :
      (∃ start < i, ∃ x : ℕ, (1 : ℕ) ≤ x ∧ start + x ≤ i ∧
          ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧
        (∀ (start len : ℕ), start < i → (1 : ℕ) ≤ len → start + len ≤ i →
          minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!) := by
    rcases invariant_inv_minSum_spec with hi0 | h
    · exfalso
      exact if_neg hi0
    · simpa using h
  rcases hMinSpec with ⟨hMinExists, hMinLower⟩

  constructor
  · -- existence carries over from `i` to `i+1`
    rcases hMinExists with ⟨start, hstartLt, x, hxpos, hxle, hsum⟩
    refine ⟨start, Nat.lt_succ_of_lt hstartLt, x, hxpos, ?_, hsum⟩
    exact le_trans hxle (Nat.le_succ i)

  · -- lower bound for all segments within `i+1`
    intro start len hstart hlen hend
    by_cases hend_i : start + len ≤ i
    · -- segment is contained in `0..i`
      have hstart_i : start < i := by
        have h1 : start + 1 ≤ start + len := Nat.add_le_add_left hlen start
        have h2 : start + 1 ≤ i := le_trans h1 hend_i
        exact lt_of_lt_of_le (Nat.lt_succ_self start) h2
      exact hMinLower start len hstart_i hlen hend_i

    · -- segment must end exactly at `i+1`
      have hend_eq : start + len = i + 1 := by
        have hge : i + 1 ≤ start + len := by
          have : ¬ start + len < i + 1 := by
            intro hlt
            have : start + len ≤ i := (Nat.lt_succ_iff.mp hlt)
            exact hend_i this
          exact le_of_not_gt this
        exact le_antisymm hend hge

      have hstart_le_i : start ≤ i := Nat.le_of_lt_succ (by simpa using hstart)
      by_cases hsi : start = i
      · -- start = i, so len = 1 and the sum is just nums[i]
        have hlen1 : len = 1 := by
          have : i + len = i + 1 := by simpa [hsi] using hend_eq
          exact Nat.add_left_cancel this
        have hcur_add_le : curMin + nums[i]! ≤ nums[i]! := by
          -- add `nums[i]!` to `curMin ≤ 0`
          simpa using (add_le_add_right if_neg_1 (nums[i]!))
        have hmin_le : minSum ≤ nums[i]! := le_trans if_neg_2 hcur_add_le
        -- rewrite the segment sum
        simpa [hsi, hlen1] using hmin_le

      · -- start < i : use curMin lower bound on the prefix ending at i, then add nums[i]
        have hstart_lt_i : start < i := lt_of_le_of_ne hstart_le_i hsi
        -- extract the nontrivial part of curMin invariant
        have hCurMinSpec :
            (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧
              (∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!) := by
          rcases invariant_inv_curMin_spec with hi0 | h
          · exfalso
            exact if_neg hi0
          · simpa using h

        have hCurMin_le_prefix : curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]! :=
          hCurMinSpec.2 start hstart_lt_i

        have hMin_le_prefix_add :
            minSum ≤ (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
          have : curMin + nums[i]! ≤ (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
            exact add_le_add_right hCurMin_le_prefix (nums[i]!)
          exact le_trans if_neg_2 this

        -- relate `len` to `i - start`
        have hlenEq : len = (i - start) + 1 := by
          have hcalc : start + ((i - start) + 1) = i + 1 := by
            calc
              start + ((i - start) + 1) = start + (i - start) + 1 := by
                simp [Nat.add_assoc]
              _ = i + 1 := by
                simp [Nat.add_sub_of_le hstart_le_i, Nat.add_assoc]
          have : start + len = start + ((i - start) + 1) := by
            calc
              start + len = i + 1 := hend_eq
              _ = start + ((i - start) + 1) := by
                simpa using hcalc.symm
          exact Nat.add_left_cancel this

        -- decompose the segment sum as prefix + last element
        have hsum_decomp :
            (∑ k ∈ Finset.range len, nums[start + k]!) =
              (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
          calc
            (∑ k ∈ Finset.range len, nums[start + k]!)
                = (∑ k ∈ Finset.range ((i - start) + 1), nums[start + k]!) := by
                    simpa [hlenEq]
            _ = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[start + (i - start)]! := by
                    simpa using
                      (Finset.sum_range_succ (f := fun k => nums[start + k]!) (n := i - start))
            _ = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
                    simp [Nat.add_sub_of_le hstart_le_i]

        exact le_trans hMin_le_prefix_add (le_of_eq hsum_decomp.symm)

theorem goal_12
    (nums : Array ℤ)
    (i : ℕ)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    intros; expose_names; exact goal_2 nums i

theorem goal_13
    (nums : Array ℤ)
    (curMax : ℤ)
    (i : ℕ)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ nums[i]! := by
  classical
  have hspec : (∃ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) = curMax) ∧
      (∀ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ curMax) := by
    rcases invariant_inv_curMax_spec with hi0 | h
    · exfalso
      exact if_neg hi0
    · exact h

  constructor
  · refine ⟨i, Nat.lt_succ_self i, ?_⟩
    have hlen : i + (1:Nat) - i = 1 := by
      -- rewrite i+1 as 1+i
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.add_sub_cancel 1 i)
    simp [hlen]

  · intro start hstart
    have hle : start ≤ i :=
      (Nat.lt_succ_iff).1 (by
        simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstart)
    rcases lt_or_eq_of_le hle with hlt | hEq
    · -- start < i
      have hsum_le_cur : (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ curMax :=
        hspec.2 start hlt
      have hsum_le_zero : (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ (0:ℤ) :=
        le_trans hsum_le_cur (le_of_lt (by simpa using if_pos_1))
      have hadd : (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! ≤ (0:ℤ) + nums[i]! :=
        add_le_add_right hsum_le_zero (nums[i]!)

      have hrewrite : (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!) =
          (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
        have hlen : i + 1 - start = (i - start) + 1 := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.succ_sub (le_of_lt hlt))
        calc
          (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!) =
              (∑ k ∈ Finset.range ((i - start) + 1), nums[start + k]!) := by
                simpa [hlen]
          _ = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[start + (i - start)]! := by
                simpa [Finset.sum_range_succ]
          _ = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := by
                simp [Nat.add_sub_of_le (le_of_lt hlt)]

      calc
        (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!)
            = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[i]! := hrewrite
        _ ≤ (0:ℤ) + nums[i]! := hadd
        _ = nums[i]! := by simp

    · -- start = i
      rw [hEq]
      have hlen : i + (1:Nat) - i = 1 := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.add_sub_cancel 1 i)
      simp [hlen]

theorem goal_14
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    intros; expose_names; exact goal_9 nums curMin i invariant_inv_curMin_spec if_neg if_neg_2

theorem goal_15
    (nums : Array ℤ)
    (curMax : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    (if_neg_1 : nums[i]! ≤ maxSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
  -- Extract the nontrivial maxSum spec at index `i` (since `i ≠ 0`).
  have hmaxSpec :
      (∃ start < i, ∃ x : ℕ, (1 : ℕ) ≤ x ∧ start + x ≤ i ∧
        ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧
      (∀ (start len : ℕ), start < i → (1 : ℕ) ≤ len → start + len ≤ i →
        ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum) := by
    rcases invariant_inv_maxSum_spec with hi0 | h
    · exfalso
      exact if_neg hi0
    · simpa using h

  refine And.intro ?exist ?bound

  · -- Existence: reuse the witness from the prefix of length `i`.
    rcases hmaxSpec.1 with ⟨start, hstart, x, hx1, hle, hsum⟩
    refine ⟨start, ?_, x, hx1, ?_, hsum⟩
    · exact Nat.lt_trans hstart (Nat.lt_succ_self i)
    · exact le_trans hle (Nat.le_succ i)

  · -- Maximality: consider any segment within the prefix of length `i+1`.
    intro start len hstart hlen hle
    have hle' : start + len ≤ i ∨ start + len = i + 1 := by
      -- Since `start+len ≤ i+1`, either it is ≤ i or it is exactly i+1.
      simpa [Nat.succ_eq_add_one] using (Nat.le_or_eq_of_le_succ hle)
    cases hle' with
    | inl hle_i =>
        -- Segment is contained in the first `i` elements.
        have hpos : 0 < len := lt_of_lt_of_le Nat.zero_lt_one hlen
        have hstart_i : start < i := by
          have : start < start + len := Nat.lt_add_of_pos_right hpos
          exact lt_of_lt_of_le this hle_i
        exact hmaxSpec.2 start len hstart_i hlen hle_i
    | inr hEq =>
        -- Segment reaches the new index `i`.
        have hlenEq : len = i + 1 - start := by
          -- Subtract `start` from both sides of `start + len = i+1`.
          have := congrArg (fun t => t - start) hEq
          simpa [Nat.add_sub_cancel_left] using this
        -- Use the bound on any segment ending at `i` when `curMax < 0`.
        have hEndAtI : ∀ s < i + 1,
            (∑ k ∈ Finset.range (i + 1 - s), nums[s + k]!) ≤ nums[i]! := by
          have h13 := (goal_13 nums curMax i invariant_inv_curMax_spec if_neg if_pos_1)
          exact h13.2
        -- Rewrite to the canonical length `i+1-start`, then bound by `nums[i]! ≤ maxSum`.
        calc
          (∑ k ∈ Finset.range len, nums[start + k]!)
              = (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!) := by
                  simp [hlenEq]
          _ ≤ nums[i]! := by
                exact hEndAtI start (by simpa using hstart)
          _ ≤ maxSum := if_neg_1

theorem goal_16
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (minSum : ℤ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_pos_2 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMin + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → curMin + nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    intros; expose_names; exact
        goal_6 nums curMin i minSum invariant_inv_curMin_spec invariant_inv_minSum_spec if_neg
          if_neg_2 if_pos_2

theorem goal_17
    (nums : Array ℤ)
    (i : ℕ)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    intros; expose_names; exact goal_12 nums i

theorem goal_18
    (nums : Array ℤ)
    (curMax : ℤ)
    (i : ℕ)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ nums[i]! := by
    intros; expose_names; exact goal_13 nums curMax i invariant_inv_curMax_spec if_neg if_pos_1

theorem goal_19
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    intros; expose_names; exact goal_9 nums curMin i invariant_inv_curMin_spec if_neg if_neg_2

theorem goal_20
    (nums : Array ℤ)
    (curMax : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : curMax < OfNat.ofNat 0)
    (if_neg_1 : nums[i]! ≤ maxSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    intros; expose_names; exact
        goal_15 nums curMax i maxSum invariant_inv_curMax_spec invariant_inv_maxSum_spec if_neg
          if_pos_1 if_neg_1

theorem goal_21
    (nums : Array ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (minSum : ℤ)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_neg_3 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    intros; expose_names; exact
        goal_11 nums curMin i minSum invariant_inv_curMin_spec invariant_inv_minSum_spec if_neg
          if_neg_2 if_neg_3

theorem goal_22
    (nums : Array ℤ)
    (i : ℕ)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    intros; expose_names; exact goal_17 nums i

theorem goal_23
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_3 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
  classical
  have hcurMaxSpec :
      (∃ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) = curMax) ∧
        (∀ start < i, (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ curMax) := by
    rcases invariant_inv_curMax_spec with h0 | h1
    · exfalso
      exact if_neg h0
    · exact h1

  rcases hcurMaxSpec.1 with ⟨start0, hstart0lt, hstart0sum⟩

  constructor
  · refine ⟨start0, Nat.lt_succ_of_lt hstart0lt, ?_⟩
    have hle0 : start0 ≤ i := Nat.le_of_lt hstart0lt
    have hlen0 : i + 1 - start0 = (i - start0).succ := by
      simpa using (Nat.succ_sub (m := i) (n := start0) hle0)
    have hidx0 : start0 + (i - start0) = i := by
      calc
        start0 + (i - start0) = (i - start0) + start0 := by
          ac_rfl
        _ = i := Nat.sub_add_cancel hle0

    calc
      (∑ k ∈ Finset.range (i + 1 - start0), nums[start0 + k]!)
          = ∑ k ∈ Finset.range ((i - start0).succ), nums[start0 + k]! := by
              simpa [hlen0]
      _ = (∑ k ∈ Finset.range (i - start0), nums[start0 + k]!) + nums[start0 + (i - start0)]! := by
            simpa using
              (Finset.sum_range_succ (f := fun k => nums[start0 + k]!) (n := i - start0))
      _ = curMax + nums[i]! := by
            simpa [hstart0sum, hidx0, add_assoc, add_comm, add_left_comm]

  · intro start hstartLt
    have hstartLe : start ≤ i := Nat.le_of_lt_succ hstartLt
    by_cases hsi : start = i
    · subst hsi
      have hle : nums[start]! ≤ curMax + nums[start]! := by
        linarith
      -- simplify the segment sum of length 1
      simpa using hle
    · have hlt : start < i := Nat.lt_of_le_of_ne hstartLe hsi
      have hold : (∑ k ∈ Finset.range (i - start), nums[start + k]!) ≤ curMax :=
        hcurMaxSpec.2 start hlt
      have hlen : i + 1 - start = (i - start).succ := by
        simpa using (Nat.succ_sub (m := i) (n := start) (Nat.le_of_lt hlt))
      have hidx : start + (i - start) = i := by
        have hle : start ≤ i := Nat.le_of_lt hlt
        calc
          start + (i - start) = (i - start) + start := by
            ac_rfl
          _ = i := Nat.sub_add_cancel hle

      calc
        (∑ k ∈ Finset.range (i + 1 - start), nums[start + k]!)
            = (∑ k ∈ Finset.range (i - start), nums[start + k]!) + nums[start + (i - start)]! := by
                simpa [hlen] using
                  (Finset.sum_range_succ (f := fun k => nums[start + k]!) (n := i - start))
        _ ≤ curMax + nums[i]! := by
              simpa [hidx] using (add_le_add_right hold (nums[i]!))



theorem goal_24
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_pos_3 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_25
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_pos_3 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMax + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_26
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_pos_3 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_27
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_neg_2 : minSum ≤ nums[i]!)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    sorry

theorem goal_28
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_neg_2 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_29
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_neg_2 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_30
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_neg_2 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMax + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_31
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_pos_2 : OfNat.ofNat 0 < curMin)
    (if_neg_2 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_32
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_neg_3 : minSum ≤ curMin + nums[i]!)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    sorry

theorem goal_33
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_neg_3 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_34
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_neg_3 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_35
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_neg_3 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMax + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_36
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (if_pos_1 : maxSum < curMax + nums[i]!)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMin ≤ OfNat.ofNat 0)
    (if_neg_3 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_37
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_pos_2 : nums[i]! < minSum)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    sorry

theorem goal_38
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_pos_2 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_39
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_pos_2 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_40
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_pos_2 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    sorry

theorem goal_41
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_pos_2 : nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_42
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_neg_3 : minSum ≤ nums[i]!)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    sorry

theorem goal_43
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_neg_3 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_44
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_neg_3 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_45
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_neg_3 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    sorry

theorem goal_46
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_pos_1 : OfNat.ofNat 0 < curMin)
    (if_neg_3 : minSum ≤ nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_47
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_pos_1 : curMin + nums[i]! < minSum)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    sorry

theorem goal_48
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_pos_1 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_49
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_pos_1 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_50
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_pos_1 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    sorry

theorem goal_51
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_pos_1 : curMin + nums[i]! < minSum)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = curMin + nums[i]!) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → curMin + nums[i]! ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_52
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_neg_4 : minSum ≤ curMin + nums[i]!)
    : ∑ j ∈ Finset.range i, nums[j]! + nums[i]! = ∑ j ∈ Finset.range (i + OfNat.ofNat 1), nums[j]! := by
    sorry

theorem goal_53
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_neg_4 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMax + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! ≤ curMax + nums[i]! := by
    sorry

theorem goal_54
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_neg_4 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! = curMin + nums[i]!) ∧ ∀ start < i + OfNat.ofNat 1, curMin + nums[i]! ≤ ∑ k ∈ Finset.range (i + OfNat.ofNat 1 - start), nums[start + k]! := by
    sorry

theorem goal_55
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_neg_4 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum := by
    sorry

theorem goal_56
    (nums : Array ℤ)
    (curMax : ℤ)
    (curMin : ℤ)
    (i : ℕ)
    (maxSum : ℤ)
    (minSum : ℤ)
    (invariant_inv_i_le_n : i ≤ nums.size)
    (invariant_inv_curMax_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMax) ∧ ∀ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! ≤ curMax)
    (invariant_inv_curMin_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∑ k ∈ Finset.range (i - start), nums[start + k]! = curMin) ∧ ∀ start < i, curMin ≤ ∑ k ∈ Finset.range (i - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = maxSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → ∑ k ∈ Finset.range len, nums[start + k]! ≤ maxSum)
    (invariant_inv_minSum_spec : i = OfNat.ofNat 0 ∨ (∃ start < i, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i → OfNat.ofNat 1 ≤ len → start + len ≤ i → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_min_le_curMin : minSum ≤ curMin)
    (if_pos : i < nums.size)
    (if_neg : ¬i = OfNat.ofNat 0)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (invariant_inv_max_ge_curMax : curMax ≤ maxSum)
    (if_neg_1 : OfNat.ofNat 0 ≤ curMax)
    (if_neg_2 : curMax + nums[i]! ≤ maxSum)
    (if_neg_3 : curMin ≤ OfNat.ofNat 0)
    (if_neg_4 : minSum ≤ curMin + nums[i]!)
    : (∃ start < i + OfNat.ofNat 1, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i + OfNat.ofNat 1 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i + OfNat.ofNat 1 → OfNat.ofNat 1 ≤ len → start + len ≤ i + OfNat.ofNat 1 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]! := by
    sorry

theorem goal_57
    (nums : Array ℤ)
    (minSum : ℤ)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (i_4 : ℤ)
    (i_5 : ℤ)
    (total_1 : ℤ)
    (if_pos : i_4 < OfNat.ofNat 0)
    (invariant_inv_min_le_curMin : minSum ≤ i_2)
    (invariant_inv_i_le_n : i_3 ≤ nums.size)
    (invariant_inv_minSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_curMax_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_1) ∧ ∀ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! ≤ i_1)
    (invariant_inv_curMin_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_2) ∧ ∀ start < i_3, i_2 ≤ ∑ k ∈ Finset.range (i_3 - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = i_4) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (done_1 : nums.size ≤ i_3)
    (invariant_inv_max_ge_curMax : i_1 ≤ i_4)
    (snd_eq : minSum = i_5 ∧ ∑ j ∈ Finset.range i_3, nums[j]! = total_1)
    : postcondition nums i_4 := by
    sorry

theorem goal_58
    (nums : Array ℤ)
    (minSum : ℤ)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (i_4 : ℤ)
    (i_5 : ℤ)
    (total_1 : ℤ)
    (invariant_inv_min_le_curMin : minSum ≤ i_2)
    (invariant_inv_i_le_n : i_3 ≤ nums.size)
    (invariant_inv_minSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_curMax_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_1) ∧ ∀ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! ≤ i_1)
    (invariant_inv_curMin_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_2) ∧ ∀ start < i_3, i_2 ≤ ∑ k ∈ Finset.range (i_3 - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = i_4) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (if_neg : OfNat.ofNat 0 ≤ i_4)
    (if_pos : i_4 < total_1 - i_5)
    (done_1 : nums.size ≤ i_3)
    (invariant_inv_max_ge_curMax : i_1 ≤ i_4)
    (snd_eq : minSum = i_5 ∧ ∑ j ∈ Finset.range i_3, nums[j]! = total_1)
    : postcondition nums (total_1 - i_5) := by
    sorry

theorem goal_59
    (nums : Array ℤ)
    (minSum : ℤ)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (i_4 : ℤ)
    (i_5 : ℤ)
    (total_1 : ℤ)
    (invariant_inv_min_le_curMin : minSum ≤ i_2)
    (invariant_inv_i_le_n : i_3 ≤ nums.size)
    (invariant_inv_minSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = minSum) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → minSum ≤ ∑ k ∈ Finset.range len, nums[start + k]!)
    (invariant_inv_curMax_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_1) ∧ ∀ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! ≤ i_1)
    (invariant_inv_curMin_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∑ k ∈ Finset.range (i_3 - start), nums[start + k]! = i_2) ∧ ∀ start < i_3, i_2 ≤ ∑ k ∈ Finset.range (i_3 - start), nums[start + k]!)
    (invariant_inv_maxSum_spec : i_3 = OfNat.ofNat 0 ∨ (∃ start < i_3, ∃ (x : ℕ), OfNat.ofNat 1 ≤ x ∧ start + x ≤ i_3 ∧ ∑ k ∈ Finset.range x, nums[start + k]! = i_4) ∧ ∀ (start len : ℕ), start < i_3 → OfNat.ofNat 1 ≤ len → start + len ≤ i_3 → ∑ k ∈ Finset.range len, nums[start + k]! ≤ i_4)
    (require_1 : OfNat.ofNat 0 < nums.size)
    (if_neg : OfNat.ofNat 0 ≤ i_4)
    (if_neg_1 : total_1 ≤ i_4 + i_5)
    (done_1 : nums.size ≤ i_3)
    (invariant_inv_max_ge_curMax : i_1 ≤ i_4)
    (snd_eq : minSum = i_5 ∧ ∑ j ∈ Finset.range i_3, nums[j]! = total_1)
    : postcondition nums i_4 := by
    sorry


set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 1)))


prove_correct MaxSumCircularSubarray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums)
  exact (goal_1 nums)
  exact (goal_2 nums i)
  exact (goal_3 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec if_pos if_neg if_pos_2 if_pos_1 if_pos_3)
  exact (goal_4 nums curMin i invariant_inv_curMin_spec if_neg if_neg_1)
  exact (goal_5 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec if_pos if_neg if_pos_2 if_pos_1 if_pos_3)
  exact (goal_6 nums curMin i minSum invariant_inv_curMin_spec invariant_inv_minSum_spec if_neg if_neg_1 if_pos_3)
  exact (goal_7 nums i)
  exact (goal_8 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec if_pos if_neg if_pos_2 if_pos_1 if_neg_2)
  exact (goal_9 nums curMin i invariant_inv_curMin_spec if_neg if_neg_1)
  exact (goal_10 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec if_pos if_neg if_pos_2 if_pos_1 if_neg_2)
  exact (goal_11 nums curMin i minSum invariant_inv_curMin_spec invariant_inv_minSum_spec if_neg if_neg_1 if_neg_2)
  exact (goal_12 nums i)
  exact (goal_13 nums curMax i invariant_inv_curMax_spec if_neg if_pos_1)
  exact (goal_14 nums curMin i invariant_inv_curMin_spec if_neg if_neg_2)
  exact (goal_15 nums curMax i maxSum invariant_inv_curMax_spec invariant_inv_maxSum_spec if_neg if_pos_1 if_neg_1)
  exact (goal_16 nums curMin i minSum invariant_inv_curMin_spec invariant_inv_minSum_spec if_neg if_neg_2 if_pos_2)
  exact (goal_17 nums i)
  exact (goal_18 nums curMax i invariant_inv_curMax_spec if_neg if_pos_1)
  exact (goal_19 nums curMin i invariant_inv_curMin_spec if_neg if_neg_2)
  exact (goal_20 nums curMax i maxSum invariant_inv_curMax_spec invariant_inv_maxSum_spec if_neg if_pos_1 if_neg_1)
  exact (goal_21 nums curMin i minSum invariant_inv_curMin_spec invariant_inv_minSum_spec if_neg if_neg_2 if_neg_3)
  exact (goal_22 nums i)
  exact (goal_23 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec if_pos if_neg if_pos_1 if_neg_1 if_pos_3)
  exact (goal_24 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_pos_3)
  exact (goal_25 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_pos_3)
  exact (goal_26 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_pos_3)
  exact (goal_27 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_neg_2)
  exact (goal_28 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_neg_2)
  exact (goal_29 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_neg_2)
  exact (goal_30 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_neg_2)
  exact (goal_31 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_pos_2 if_neg_2)
  exact (goal_32 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3)
  exact (goal_33 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3)
  exact (goal_34 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3)
  exact (goal_35 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3)
  exact (goal_36 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg if_pos_1 require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3)
  exact (goal_37 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_pos_2)
  exact (goal_38 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_pos_2)
  exact (goal_39 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_pos_2)
  exact (goal_40 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_pos_2)
  exact (goal_41 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_pos_2)
  exact (goal_42 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_neg_3)
  exact (goal_43 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_neg_3)
  exact (goal_44 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_neg_3)
  exact (goal_45 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_neg_3)
  exact (goal_46 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_pos_1 if_neg_3)
  exact (goal_47 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_48 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_49 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_50 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_51 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_52 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_53 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_54 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_55 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_56 nums curMax curMin i maxSum minSum invariant_inv_i_le_n invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec invariant_inv_minSum_spec invariant_inv_min_le_curMin if_pos if_neg require_1 invariant_inv_max_ge_curMax if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_57 nums minSum i_1 i_2 i_3 i_4 i_5 total_1 if_pos invariant_inv_min_le_curMin invariant_inv_i_le_n invariant_inv_minSum_spec invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec require_1 done_1 invariant_inv_max_ge_curMax snd_eq)
  exact (goal_58 nums minSum i_1 i_2 i_3 i_4 i_5 total_1 invariant_inv_min_le_curMin invariant_inv_i_le_n invariant_inv_minSum_spec invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec require_1 if_neg if_pos done_1 invariant_inv_max_ge_curMax snd_eq)
  exact (goal_59 nums minSum i_1 i_2 i_3 i_4 i_5 total_1 invariant_inv_min_le_curMin invariant_inv_i_le_n invariant_inv_minSum_spec invariant_inv_curMax_spec invariant_inv_curMin_spec invariant_inv_maxSum_spec require_1 if_neg if_neg_1 done_1 invariant_inv_max_ge_curMax snd_eq)
end Proof
