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
    SingleNumber: Find the unique integer in a non-empty list where all other integers appear exactly twice.

    Natural language breakdown:
    1. The input is a list of integers `nums`.
    2. There exists exactly one integer that occurs in `nums` exactly once.
    3. Every other integer occurs either zero times (not present) or exactly twice.
    4. The function returns the integer that occurs exactly once.
-/

section Specs
-- There is exactly one value with count = 1, and every other value has count 0 or 2.
-- This property already implies the list is non-empty.
def hasSingleWithPairs (nums : List Int) : Prop :=
  ∃ x : Int,
    nums.count x = 1 ∧
    (∀ y : Int, nums.count y = 1 → y = x) ∧
    (∀ y : Int, y ≠ x → (nums.count y = 0 ∨ nums.count y = 2))

-- Preconditions: the input list satisfies the intended “pairs except one” shape.
def precondition (nums : List Int) : Prop :=
  hasSingleWithPairs nums

-- Postcondition: the returned value is exactly the unique element with count = 1.
def postcondition (nums : List Int) (result : Int) : Prop :=
  nums.count result = 1 ∧ (∀ y : Int, nums.count y = 1 → y = result)
end Specs

section Impl
method SingleNumber (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: singleton list (degenerate valid case)
def test1_nums : List Int := [7]
def test1_Expected : Int := 7

-- Test case 2: simple pair + single
def test2_nums : List Int := [2, 2, 1]
def test2_Expected : Int := 1

-- Test case 3: includes zero as the unique element
def test3_nums : List Int := [5, 0, 5]
def test3_Expected : Int := 0

-- Test case 4: includes negative numbers; unique is negative
def test4_nums : List Int := [-3, 4, 4]
def test4_Expected : Int := -3

-- Test case 5: multiple pairs, unique in the middle
def test5_nums : List Int := [10, 1, 10, 2, 2]
def test5_Expected : Int := 1

-- Test case 6: unique at the end
def test6_nums : List Int := [9, 9, 8, 8, 6]
def test6_Expected : Int := 6

-- Test case 7: many pairs, unique is large positive
def test7_nums : List Int := [1000, 1, 1, 2, 2, 3, 3]
def test7_Expected : Int := 1000

-- Test case 8: unique is zero, with additional pairs
def test8_nums : List Int := [0, -1, -1, 5, 5]
def test8_Expected : Int := 0

-- Test case 9: unique is negative with two other pairs
def test9_nums : List Int := [-10, 6, 6, 7, 7]
def test9_Expected : Int := -10

-- Recommend to validate: precondition test1_nums, postcondition test1_nums test1_Expected, postcondition test9_nums test9_Expected
end TestCases
