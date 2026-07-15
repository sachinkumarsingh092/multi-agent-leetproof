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
    1752. Check if Array Is Sorted and Rotated: decide whether an array can be obtained by rotating a non-decreasingly sorted array.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. We are given an array `nums` of integers; duplicates are allowed.
    2. A non-decreasingly sorted array has no adjacent decrease: for each valid i, A[i] ≤ A[i+1].
    3. Rotating an array by x positions shifts elements cyclically; rotation by 0 leaves the array unchanged.
    4. The input `nums` is valid iff there exists some rotation of `nums` that is non-decreasing.
    5. Equivalent circular characterization: scanning the array cyclically, there is at most one index i where nums[i] > nums[(i+1) mod n].
    6. Arrays of length 0 or 1 are always considered sorted-and-rotated.
-/

section Specs
-- A “drop” is a strict decrease from an element to its cyclic successor.
-- We define it as a Prop so it can be used in specifications.

def isDrop (nums : Array Int) (i : Nat) : Prop :=
  nums.size > 0 ∧ i < nums.size ∧ nums[(i + 1) % nums.size]! < nums[i]!

-- `rotSortedProp nums` holds exactly when `nums` is sorted-and-rotated in the sense of the problem.
-- Using the standard circular-drop characterization: at most one drop.

def rotSortedProp (nums : Array Int) : Prop :=
  nums.size ≤ 1 ∨ (∀ (i : Nat) (j : Nat), isDrop nums i → isDrop nums j → i = j)

-- No input constraints.

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ rotSortedProp nums) ∧
  (result = false ↔ ¬ rotSortedProp nums)
end Specs

section Impl
method CheckSortedAndRotated (nums : Array Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  pure true

end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [3,4,5,1,2] -> true

def test1_nums : Array Int := #[3, 4, 5, 1, 2]

def test1_Expected : Bool := true

-- Test case 2: Example 2
-- nums = [2,1,3,4] -> false

def test2_nums : Array Int := #[2, 1, 3, 4]

def test2_Expected : Bool := false

-- Test case 3: Example 3
-- nums = [1,2,3] -> true

def test3_nums : Array Int := #[1, 2, 3]

def test3_Expected : Bool := true

-- Test case 4: Empty array (degenerate)

def test4_nums : Array Int := #[]

def test4_Expected : Bool := true

-- Test case 5: Singleton array (degenerate)

def test5_nums : Array Int := #[42]

def test5_Expected : Bool := true

-- Test case 6: All equal elements (duplicates; any rotation is the same)

def test6_nums : Array Int := #[7, 7, 7, 7]

def test6_Expected : Bool := true

-- Test case 7: Sorted but not rotated (0 rotation)

def test7_nums : Array Int := #[0, 0, 1, 2, 2, 5]

def test7_Expected : Bool := true

-- Test case 8: Rotated with duplicates, still valid
-- Original sorted: [1,1,2,3,3], rotate by 3 -> [3,3,1,1,2]

def test8_nums : Array Int := #[3, 3, 1, 1, 2]

def test8_Expected : Bool := true

-- Test case 9: Two drops in the cyclic scan -> invalid
-- Drops at 0: 3>1 and at 2: 2>0

def test9_nums : Array Int := #[3, 1, 2, 0]

def test9_Expected : Bool := false
end TestCases
