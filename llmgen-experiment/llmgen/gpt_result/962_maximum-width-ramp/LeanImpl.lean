import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (nums : Array Int) : Nat :=
  let n := nums.size
  if hsmall : n ≤ 1 then
    0
  else
    -- Build a stack of indices with strictly decreasing values (by nums[i]).
    let rec buildStack (i : Nat) (st : List Nat) : List Nat :=
      if h : i < n then
        let x := nums[i]!
        match st with
        | [] => buildStack (i + 1) [i]
        | j :: _ =>
          if x < nums[j]! then
            buildStack (i + 1) (i :: st)
          else
            buildStack (i + 1) st
      else
        st
    termination_by n - i

    -- Pop from stack while it forms a ramp with j, updating best.
    let rec popWhile (j : Nat) (st : List Nat) (best : Nat) : List Nat × Nat :=
      match st with
      | [] => ([], best)
      | i :: rest =>
        if nums[i]! ≤ nums[j]! then
          popWhile j rest (Nat.max best (j - i))
        else
          (st, best)
    termination_by st

    -- Scan from right to left.
    let rec scanRight (j : Nat) (st : List Nat) (best : Nat) : Nat :=
      if hj : j < n then
        let (st', best') := popWhile j st best
        match j with
        | 0 => best'
        | j' + 1 => scanRight j' st' best'
      else
        best
    termination_by j

    let st := buildStack 0 []
    scanRight (n - 1) st 0
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

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (n : ℕ)
    (hsmall : n ≤ 1)
    (himpl : implementation nums = 0)
    (w : ℕ)
    (hw : IsRampWidth nums w)
    : ¬IsRampWidth nums w := by
    sorry

theorem correctness_goal_1
    (nums : Array ℤ)
    (n : ℕ)
    (himpl : implementation nums = implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0)
    : implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0 = 0 ∨
  IsRampWidth nums (implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0) := by
  -- rewrite the goal to the corresponding property about `implementation nums`
  have hres : implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0 = implementation nums := by
    simpa using (Eq.symm himpl)

  have himpl_spec : implementation nums = 0 ∨ IsRampWidth nums (implementation nums) := by
    classical
    by_cases hs : nums.size ≤ 1
    · -- small array: implementation returns 0
      left
      simp [implementation, hs]
    · -- main case: implementation is scanRight from the end with best = 0
      have h0 : (0 = 0 ∨ IsRampWidth nums 0) := Or.inl rfl
      -- `simp` reduces `implementation` to its else-branch call to `scanRight`.
      simpa [implementation, hs] using
        (scanRight_preserves_zero_or_rampWidth (nums := nums)
          (j := nums.size - 1)
          (st := implementation.buildStack nums nums.size 0 [])
          (best := 0)
          h0)

  -- transfer back to the original scanRight expression
  simpa [hres] using himpl_spec

theorem correctness_goal_2_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (n : ℕ)
    (hsmall : ¬n ≤ 1)
    (himpl : implementation nums = implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0)
    (w : ℕ)
    (hw : IsRampWidth nums w)
    (hs : ¬nums.size ≤ 1)
    : ∀ (w : ℕ),
  IsRampWidth nums w →
    w ≤ implementation.scanRight nums nums.size (nums.size - 1) (implementation.buildStack nums nums.size 0 []) 0 := by
    sorry

theorem correctness_goal_2
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (n : ℕ)
    (hsmall : ¬n ≤ 1)
    (himpl : implementation nums = implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0)
    : ∀ (w : ℕ), IsRampWidth nums w → w ≤ implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0 := by
  intro w hw
  -- Reduce to a bound by the actual implementation result.
  have h_w_le_impl : w ≤ implementation nums := by
    -- Case split on the real array size used inside `implementation`.
    by_cases hs : nums.size ≤ 1
    · -- In the small-size case, there are no ramps.
      have h_no : ¬ IsRampWidth nums w := by
        -- Any ramp requires two distinct indices below `nums.size`.
        -- Contradicts `nums.size ≤ 1`.
        expose_names; simp only [IsRamp, IsRampWidth, precondition, postcondition]
        rw [Array.size_eq_length_toList]
        intros; expose_names; try simp_all; try grind
      have : False := h_no hw
      -- implementation is 0 in this branch
      simp [implementation, hs] at *
    · -- Non-small case: `implementation` is the `scanRight` result with `n = nums.size`.
      have hscan_spec : ∀ (w : ℕ), IsRampWidth nums w →
          w ≤ implementation.scanRight nums nums.size (nums.size - 1)
                (implementation.buildStack nums nums.size 0 []) 0 := by
        expose_names; exact (correctness_goal_2_0 nums h_precond n hsmall himpl w hw hs)
      simpa [implementation, hs] using (hscan_spec w hw)
  -- Rewrite `implementation nums` to the stated RHS using `himpl`.
  simpa [himpl] using h_w_le_impl

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation (nums)) := by
  classical
  let n := nums.size
  by_cases hsmall : n ≤ 1
  · -- small arrays
    have himpl : implementation nums = 0 := by
      simp [implementation, n, hsmall]
    rw [himpl]
    refine And.intro ?_ ?_
    · exact Or.inl rfl
    · intro w hw
      have hno : False := by
        have hnone : ¬ IsRampWidth nums w := by
          -- prove no ramp widths exist when size ≤ 1
          expose_names; exact (correctness_goal_0 nums h_precond n hsmall himpl w hw)
        exact (hnone hw)
      exact False.elim hno
  · -- n > 1
    have himpl : implementation nums = implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0 := by
      simp [implementation, n, hsmall]
    rw [himpl]
    refine And.intro ?_ ?_
    · -- witness or zero
      have h_witness :
          (implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0 = 0 ∨
            IsRampWidth nums
              (implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0)) := by
        expose_names; exact (correctness_goal_1 nums n himpl)
      exact h_witness
    · -- maximality
      have h_max : ∀ w, IsRampWidth nums w →
          w ≤ implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0 := by
        expose_names; exact (correctness_goal_2 nums h_precond n hsmall himpl)
      exact h_max
end Proof
