import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    ContainerWithMostWater: given an array of line heights, return the maximum water area.
    Natural language breakdown:
    1. The input is an array `height` of nonnegative integers, interpreted as vertical lines at x-coordinates 0..n-1.
    2. For any two distinct indices i < j, a container can be formed with width (j - i).
    3. The container height is limited by the shorter line: min(height[i], height[j]).
    4. The area (water amount) for a pair (i, j) is (j - i) * min(height[i], height[j]).
    5. The desired result is the maximum area over all index pairs with i < j.
    6. If the array has fewer than 2 elements, no valid container exists; we therefore require size ≥ 2.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

-- Area contributed by a particular pair of indices (i,j).
-- Uses Nat throughout since heights and areas are nonnegative.
-- Defined as 0 if indices are out of range or not ordered; preconditions/postconditions will use it only with i<j<size.
def pairArea (height : Array Nat) (i : Nat) (j : Nat) : Nat :=
  (j - i) * Nat.min (height[i]!) (height[j]!)

-- Precondition: at least two lines exist.
def precondition (height : Array Nat) : Prop :=
  height.size ≥ 2

-- Postcondition: result is an achievable maximum area.
-- 1) There exists a pair i<j within bounds whose area equals result.
-- 2) For all pairs i<j within bounds, their area is ≤ result.
def postcondition (height : Array Nat) (result : Nat) : Prop :=
  (∃ (i : Nat) (j : Nat), i < j ∧ j < height.size ∧ pairArea height i j = result) ∧
  (∀ (i : Nat) (j : Nat), i < j → j < height.size → pairArea height i j ≤ result)
end Specs

section Impl
def implementation (height : Array Nat) : Nat :=
  let n := height.size
  if h : n < 2 then
    0
  else
    let rec go (l r best : Nat) : Nat :=
      if hlt : l < r then
        let hl := height[l]!
        let hr := height[r]!
        let area := (r - l) * Nat.min hl hr
        let best' := Nat.max best area
        if hl ≤ hr then
          go (l + 1) r best'
        else
          go l (r - 1) best'
      else
        best
    termination_by r - l
    go 0 (n - 1) 0
end Impl

section TestCases
-- Test case 1: Example 1 from prompt
-- height = [1,8,6,2,5,4,8,3,7], expected max area = 49
-- (i=1,j=8) => width=7, min(8,7)=7, area=49

def test1_height : Array Nat := #[1, 8, 6, 2, 5, 4, 8, 3, 7]

def test1_Expected : Nat := 49

-- Test case 2: Example 2 from prompt
-- height = [1,1], only pair gives area 1

def test2_height : Array Nat := #[1, 1]

def test2_Expected : Nat := 1

-- Test case 3: Minimal size with a zero
-- height = [0,0] => area 0

def test3_height : Array Nat := #[0, 0]

def test3_Expected : Nat := 0

-- Test case 4: Strictly increasing
-- Best is (1,4): width 3, min(2,5)=2 => 6

def test4_height : Array Nat := #[1, 2, 3, 4, 5]

def test4_Expected : Nat := 6

-- Test case 5: Strictly decreasing
-- Best is (0,3): width 3, min(5,2)=2 => 6

def test5_height : Array Nat := #[5, 4, 3, 2, 1]

def test5_Expected : Nat := 6

-- Test case 6: All equal
-- height = [3,3,3,3] => best endpoints (0,3): width 3 * 3 = 9

def test6_height : Array Nat := #[3, 3, 3, 3]

def test6_Expected : Nat := 9

-- Test case 7: Zeros inside, tall endpoints
-- height = [5,0,0,0,5] => width 4 * min(5,5)=20

def test7_height : Array Nat := #[5, 0, 0, 0, 5]

def test7_Expected : Nat := 20

-- Test case 8: Multiple maxima possible
-- height = [2,4,2,4,2]
-- (0,4): width 4 * min(2,2)=8
-- (1,3): width 2 * min(4,4)=8

def test8_height : Array Nat := #[2, 4, 2, 4, 2]

def test8_Expected : Nat := 8

-- Test case 9: Classic mixed small array
-- height = [1,2,1] => best (0,2): width 2 * min(1,1)=2

def test9_height : Array Nat := #[1, 2, 1]

def test9_Expected : Nat := 2
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_height), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_height), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_height), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_height), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_height), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_height), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_height), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_height), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_height), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0
    (height : Array ℕ)
    (h_precond : precondition height)
    (hn2 : ¬height.size < 2)
    (himpl : implementation height = implementation.go height 0 (height.size - 1) 0)
    : postcondition height (implementation.go height 0 (height.size - 1) 0) := by
    sorry

theorem correctness_goal
    (height : Array Nat)
    (h_precond : precondition height)
    : postcondition height (implementation (height)) := by
  classical
  have hn2 : ¬ height.size < 2 := by
    exact Nat.not_lt.mpr h_precond
  have himpl : implementation height = implementation.go height 0 (height.size - 1) 0 := by
    simp [implementation, hn2]
  have hpost : postcondition height (implementation.go height 0 (height.size - 1) 0) := by
    expose_names; exact (correctness_goal_0 height h_precond hn2 himpl)
  simpa [himpl] using hpost
end Proof
