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

section Specs
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
method ContainerWithMostWater (height : Array Nat)
  return (result : Nat)
  require precondition height
  ensures postcondition height result
  do
  -- Placeholder body only; correctness proof is provided separately.
  pure 0

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
