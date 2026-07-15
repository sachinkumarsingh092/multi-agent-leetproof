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
  pure 0

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
