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
    TwoSum: Return indices of two distinct list elements whose sum equals a target.

    Natural language breakdown:
    1. Input is a list of integers `nums` and an integer `target`.
    2. A solution is a pair of natural-number indices (i, j) such that i and j are valid indices into nums.
    3. The indices must be distinct and ordered: i < j.
    4. The values at those indices must sum to the target: nums[i] + nums[j] = target.
    5. The problem guarantees there is exactly one such ordered solution pair; this is modeled as a precondition.
    6. The returned result must be that unique solution pair.
-/

section Specs
-- (i,j) is a valid TwoSum witness for (nums,target) when it is ordered, in-bounds, and sums to target.
-- Note: `j < nums.length` together with `i < j` implies `i < nums.length`, so we do not repeat it.
def IsTwoSumWitness (nums : List Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

-- There exists exactly one witness pair with i<j.
def HasUniqueTwoSum (nums : List Int) (target : Int) : Prop :=
  (∃ i : Nat, ∃ j : Nat, IsTwoSumWitness nums target i j) ∧
  (∀ i1 : Nat, ∀ j1 : Nat, ∀ i2 : Nat, ∀ j2 : Nat,
    IsTwoSumWitness nums target i1 j1 →
    IsTwoSumWitness nums target i2 j2 →
    (i1 = i2 ∧ j1 = j2))

-- Preconditions:
-- 1) The input admits exactly one solution pair (i,j) with i<j.
def precondition (nums : List Int) (target : Int) : Prop :=
  HasUniqueTwoSum nums target

-- Postcondition:
-- 1) The returned pair is a valid witness.
-- 2) Any other valid witness must have the same indices (so the returned pair is the unique solution).
def postcondition (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  IsTwoSumWitness nums target result.1 result.2 ∧
  (∀ i : Nat, ∀ j : Nat,
    IsTwoSumWitness nums target i j → (i = result.1 ∧ j = result.2))
end Specs

section Impl
method TwoSum (nums : List Int) (target : Int)
  return (result : Prod Nat Nat)
  require precondition nums target
  ensures postcondition nums target result
  do
  -- Placeholder implementation only.
  pure (0, 1)

end Impl

section TestCases
-- Test case 1: classic example
-- nums = [2,7,11,15], target = 9, answer = (0,1)
def test1_nums : List Int := [2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Prod Nat Nat := (0, 1)

-- Test case 2: minimal length list with duplicate values
-- nums = [5,5], target = 10
-- unique solution uses distinct indices (0,1)
def test2_nums : List Int := [5, 5]
def test2_target : Int := 10
def test2_Expected : Prod Nat Nat := (0, 1)

-- Test case 3: includes -1, 0, 1; unique solution is (-1)+3 = 2
-- nums = [-1,0,1,3], target = 2
-- only valid pair is (0,3)
def test3_nums : List Int := [-1, 0, 1, 3]
def test3_target : Int := 2
def test3_Expected : Prod Nat Nat := (0, 3)

-- Test case 4: target 0 with two zeros
-- nums = [0,4,3,0], target = 0
-- unique solution is (0,3)
def test4_nums : List Int := [0, 4, 3, 0]
def test4_target : Int := 0
def test4_Expected : Prod Nat Nat := (0, 3)

-- Test case 5: negative target
-- nums = [-1,-2,-3,-4,-5], target = -8
-- unique solution is (-3)+(-5) at indices (2,4)
def test5_nums : List Int := [-1, -2, -3, -4, -5]
def test5_target : Int := -8
def test5_Expected : Prod Nat Nat := (2, 4)

-- Test case 6: duplicates present; unique solution uses two equal values at distinct indices
-- nums = [3,3,4], target = 6
-- unique solution is (0,1)
def test6_nums : List Int := [3, 3, 4]
def test6_target : Int := 6
def test6_Expected : Prod Nat Nat := (0, 1)

-- Test case 7: solution at the tail
-- nums = [1,2,3,4,5], target = 9
-- unique solution is (3,4)
def test7_nums : List Int := [1, 2, 3, 4, 5]
def test7_target : Int := 9
def test7_Expected : Prod Nat Nat := (3, 4)

-- Test case 8: mixed signs, ensure uniqueness
-- nums = [100,-50,20,31], target = 50
-- unique solution is (0,1)
def test8_nums : List Int := [100, -50, 20, 31]
def test8_target : Int := 50
def test8_Expected : Prod Nat Nat := (0, 1)

-- Recommend to validate: uniqueness, index-bounds, sum-correctness
end TestCases
