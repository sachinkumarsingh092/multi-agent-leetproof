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
    217. Contains Duplicate: Determine whether an integer array contains any value at least twice.
    **Important: complexity should be O(n^2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array of integers `nums`.
    2. The output is a boolean.
    3. The output is `true` exactly when there exist two different indices i and j with i < j such that nums[i] = nums[j].
    4. The output is `false` exactly when for all indices i < j in range, nums[i] ≠ nums[j] (all elements are distinct).
    5. Edge cases: empty arrays and single-element arrays have no duplicates, so the result is false.
-/

section Specs
-- There is a duplicate iff two different indices within bounds have equal elements.
def HasDuplicate (nums : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat), i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasDuplicate nums) ∧
  (result = false ↔ ¬ HasDuplicate nums)
end Specs

section Impl
method ContainsDuplicate (nums: Array Int)
  return (result: Bool)
  require precondition nums
  ensures postcondition nums result
  do
  pure false

end Impl

section TestCases
-- Test case 1: example 1
-- nums = [1,2,3,1] -> true

def test1_nums : Array Int := #[1, 2, 3, 1]
def test1_Expected : Bool := true

-- Test case 2: example 2
-- nums = [1,2,3,4] -> false

def test2_nums : Array Int := #[1, 2, 3, 4]
def test2_Expected : Bool := false

-- Test case 3: example 3 (multiple duplicates)

def test3_nums : Array Int := #[1, 1, 1, 3, 3, 4, 3, 2, 4, 2]
def test3_Expected : Bool := true

-- Test case 4: empty array

def test4_nums : Array Int := #[]
def test4_Expected : Bool := false

-- Test case 5: singleton array

def test5_nums : Array Int := #[42]
def test5_Expected : Bool := false

-- Test case 6: duplicates adjacent

def test6_nums : Array Int := #[7, 7]
def test6_Expected : Bool := true

-- Test case 7: duplicates non-adjacent with negatives

def test7_nums : Array Int := #[-1, 0, 1, 2, -1]
def test7_Expected : Bool := true

-- Test case 8: all distinct including negative and zero

def test8_nums : Array Int := #[-3, -2, -1, 0, 1, 2, 3]
def test8_Expected : Bool := false

-- Test case 9: many equal elements

def test9_nums : Array Int := #[5, 5, 5, 5]
def test9_Expected : Bool := true
end TestCases
