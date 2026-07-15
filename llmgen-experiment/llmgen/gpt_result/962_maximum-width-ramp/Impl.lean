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
    MaximumWidthRamp: compute the maximum width of a ramp in an integer array.
    Natural language breakdown:
    1. The input is an array `nums` of integers.
    2. A ramp is a pair of indices (i, j) such that i < j and nums[i] ≤ nums[j].
    3. The width of a ramp (i, j) is the natural number j - i.
    4. The goal is to return the maximum width among all ramps in the array.
    5. If there is no ramp (i.e., no pair i < j with nums[i] ≤ nums[j]), the result must be 0.
    6. The result is always between 0 and nums.size - 1.
    Your algorithm should run in **O(n)** time and **O(n)** extra space.
-/

section Specs
-- A ramp predicate over indices of an array.
-- We use Nat indices and guard access with bounds.
def IsRamp (nums : Array Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! ≤ nums[j]!

-- The set of all achievable ramp widths.
def IsRampWidth (nums : Array Int) (w : Nat) : Prop :=
  ∃ (i : Nat) (j : Nat), IsRamp nums i j ∧ w = j - i

-- Precondition: no special restrictions; empty and singleton arrays are allowed.
def precondition (nums : Array Int) : Prop :=
  True

-- Postcondition: result is the maximum achievable ramp width; if none exist, it is 0.
-- We avoid defining the result as a call to a reference implementation.
def postcondition (nums : Array Int) (result : Nat) : Prop :=
  (result = 0 ∨ IsRampWidth nums result) ∧
  (∀ (w : Nat), IsRampWidth nums w → w ≤ result)
end Specs

section Impl
method MaximumWidthRamp (nums : Array Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  -- O(n) time, O(n) extra space.
  -- Algorithm:
  -- 1) Build a monotone decreasing stack of indices of prefix minima.
  -- 2) Scan j from right to left, popping while nums[stack.top] ≤ nums[j]
  --    and updating the best width.

  let n := nums.size
  if n ≤ 1 then
    return 0
  else
    -- stack stores indices (Nat) with strictly decreasing values in nums
    let mut st : Array Nat := #[]

    -- Build decreasing stack from left to right.
    let mut i : Nat := 0
    while i < n
      -- i stays within bounds
      invariant "inv_build_i_le_n" (i ≤ n)
      -- stack size is at most the number of processed indices
      invariant "inv_build_st_size_le_i" (st.size ≤ i)
      -- stack indices always point into the processed prefix [0,i)
      invariant "inv_build_st_idx_lt_i" (∀ k, k < st.size → st[k]! < i)
      -- stack indices are strictly increasing
      invariant "inv_build_st_increasing" (∀ k, k + 1 < st.size → st[k]! < st[k+1]! )
      -- corresponding values are strictly decreasing (prefix minima)
      invariant "inv_build_st_decreasing_vals" (∀ k, k + 1 < st.size → nums[st[k+1]!]! < nums[st[k]!]!)
      decreasing n - i
    do
      if st.size = 0 then
        st := st.push i
      else
        let topIdx := st[st.size - 1]!
        if nums[i]! < nums[topIdx]! then
          st := st.push i
      i := i + 1

    -- Sweep from right to left to find max width.
    let mut best : Nat := 0
    let mut j : Nat := n
    while j > 0
      -- j counts down from n to 0
      invariant "inv_sweep_j_le_n" (j ≤ n)
      -- best is always a valid width bound
      invariant "inv_sweep_best_le_n" (best ≤ n)
      -- best is either 0 or achieved by some ramp
      invariant "inv_sweep_best_feasible" (best = 0 ∨ IsRampWidth nums best)
      -- stack indices stay within array bounds
      invariant "inv_sweep_st_valid" (∀ k, k < st.size → st[k]! < n)
      invariant "inv_sweep_st_increasing" (∀ k, k + 1 < st.size → st[k]! < st[k+1]! )
      invariant "inv_sweep_st_decreasing_vals" (∀ k, k + 1 < st.size → nums[st[k+1]!]! < nums[st[k]!]!)
      -- all ramps whose right endpoint has already been swept (j0 ≥ j) are bounded by best
      invariant "inv_sweep_processed" (∀ i0 j0, j ≤ j0 → j0 < n → i0 < j0 → nums[i0]! ≤ nums[j0]! → j0 - i0 ≤ best)
      decreasing j
    do
      j := j - 1

      -- Pop all left indices that form a ramp with current j.
      let mut done : Bool := false
      while (done = false ∧ st.size > 0)
        invariant "inv_pop_st_valid" (∀ k, k < st.size → st[k]! < n)
        invariant "inv_pop_st_increasing" (∀ k, k + 1 < st.size → st[k]! < st[k+1]!)
        invariant "inv_pop_st_decreasing_vals" (∀ k, k + 1 < st.size → nums[st[k+1]!]! < nums[st[k]!]!)
        -- j is a valid in-bounds index inside this loop
        invariant "inv_pop_j_valid" (j < n)
        invariant "inv_pop_best_le_n" (best ≤ n)
        invariant "inv_pop_best_feasible" (best = 0 ∨ IsRampWidth nums best)
        -- ramps strictly to the right of j stay bounded while we pop/update using this j
        invariant "inv_pop_processed_right" (∀ i0 j0, j + 1 ≤ j0 → j0 < n → i0 < j0 → nums[i0]! ≤ nums[j0]! → j0 - i0 ≤ best)
        decreasing st.size
      do
        let leftIdx := st[st.size - 1]!
        if nums[leftIdx]! ≤ nums[j]! then
          -- update best width
          let w := j - leftIdx
          if w > best then
            best := w
          -- pop
          st := st.pop
        else
          done := true

    return best
end Impl

section TestCases
-- Test case 1: Example 1 from the prompt
-- nums = [6,0,8,2,1,5] → 4
-- (i, j) = (1, 5) gives width 4.
def test1_nums : Array Int := #[6, 0, 8, 2, 1, 5]
def test1_Expected : Nat := 4

-- Test case 2: Example 2 from the prompt
-- nums = [9,8,1,0,1,9,4,0,4,1] → 7
-- (i, j) = (2, 9) gives width 7.
def test2_nums : Array Int := #[9, 8, 1, 0, 1, 9, 4, 0, 4, 1]
def test2_Expected : Nat := 7

-- Test case 3: Empty array (degenerate)
def test3_nums : Array Int := #[]
def test3_Expected : Nat := 0

-- Test case 4: Singleton array (degenerate)
def test4_nums : Array Int := #[42]
def test4_Expected : Nat := 0

-- Test case 5: Strictly decreasing, no ramp exists
-- [5,4,3,2,1] has no i<j with nums[i] ≤ nums[j].
def test5_nums : Array Int := #[5, 4, 3, 2, 1]
def test5_Expected : Nat := 0

-- Test case 6: All equal values, widest ramp is first to last
-- size 4 → width 3.
def test6_nums : Array Int := #[7, 7, 7, 7]
def test6_Expected : Nat := 3

-- Test case 7: Strictly increasing, widest ramp is first to last
-- [1,2,3,4,5] → width 4.
def test7_nums : Array Int := #[1, 2, 3, 4, 5]
def test7_Expected : Nat := 4

-- Test case 8: Contains negative values
-- [-3,-2,-5,-1] max width ramp is (0,3): -3 ≤ -1 → width 3.
def test8_nums : Array Int := #[-3, -2, -5, -1]
def test8_Expected : Nat := 3

-- Test case 9: Multiple candidates; best uses a small left value far left
-- [2,1,2,0,1] best is (1,4): 1 ≤ 1 width 3.
def test9_nums : Array Int := #[2, 1, 2, 0, 1]
def test9_Expected : Nat := 3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MaximumWidthRamp test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MaximumWidthRamp test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MaximumWidthRamp test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MaximumWidthRamp test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MaximumWidthRamp test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MaximumWidthRamp test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MaximumWidthRamp test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MaximumWidthRamp test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MaximumWidthRamp test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MaximumWidthRamp (config := { maxMs := some 20000 })
end Pbt
