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
    TwoSumFirstPair: find the lexicographically smallest pair of indices (i, j) in an integer array whose elements sum to a target.
    Natural language breakdown:
    1. We are given an array nums of integers and an integer target.
    2. A pair of indices (i, j) is valid when 0 ≤ i < j < nums.size and nums[i] + nums[j] = target.
    3. The required output is a pair (i, j) that is valid.
    4. Among all valid pairs, the output must be lexicographically smallest: i is minimized first; among pairs with the same i, j is minimized.
    5. The input is assumed to have at least two elements.
    6. The input is assumed to admit at least one valid pair.
-/

section Specs
-- A computable/decidable predicate describing when (i,j) is a valid two-sum witness.
-- We keep it purely in terms of Array operations (no conversions).
def isTwoSumPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- Lexicographic minimality on Nat × Nat, specialized to the two-sum predicate.
-- This states that (i,j) is no larger (lexicographically) than any other valid pair.
def isLexMinTwoSumPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  isTwoSumPair nums target i j ∧
  ∀ (i' : Nat) (j' : Nat),
    isTwoSumPair nums target i' j' →
      (i < i') ∨ (i = i' ∧ j ≤ j')

-- Preconditions
-- 1) at least two elements
-- 2) existence of at least one valid pair

def precondition (nums : Array Int) (target : Int) : Prop :=
  nums.size ≥ 2 ∧
  ∃ (i : Nat) (j : Nat), isTwoSumPair nums target i j

-- Postconditions
-- result must be a valid two-sum pair and lexicographically minimal among all valid pairs.
def postcondition (nums : Array Int) (target : Int) (result : (Nat × Nat)) : Prop :=
  isLexMinTwoSumPair nums target result.1 result.2
end Specs

section Impl
method TwoSumFirstPair (nums : Array Int) (target : Int)
  return (result : (Nat × Nat))
  require precondition nums target
  ensures postcondition nums target result
  do
  pure (0, 1)  -- placeholder body

end Impl

section TestCases
-- Test case 1: typical example with a unique earliest pair
-- nums = [2,7,11,15], target = 9, answer = (0,1)
def test1_nums : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : (Nat × Nat) := (0, 1)

-- Test case 2: solution not involving index 0
-- nums = [3,2,4], target = 6, answer = (1,2)
def test2_nums : Array Int := #[3, 2, 4]
def test2_target : Int := 6
def test2_Expected : (Nat × Nat) := (1, 2)

-- Test case 3: minimal size array (boundary), exactly one pair
-- nums = [3,3], target = 6, answer = (0,1)
def test3_nums : Array Int := #[3, 3]
def test3_target : Int := 6
def test3_Expected : (Nat × Nat) := (0, 1)

-- Test case 4: includes zeros, pair uses a later zero
-- nums = [0,4,3,0], target = 0, answer = (0,3)
def test4_nums : Array Int := #[0, 4, 3, 0]
def test4_target : Int := 0
def test4_Expected : (Nat × Nat) := (0, 3)

-- Test case 5: all negative numbers
-- nums = [-1,-2,-3,-4,-5], target = -8, answer = (2,4)
def test5_nums : Array Int := #[-1, -2, -3, -4, -5]
def test5_target : Int := (-8)
def test5_Expected : (Nat × Nat) := (2, 4)

-- Test case 6: multiple solutions, lexicographically smallest chooses smallest i then smallest j
-- nums = [1,5,1,5], target = 6, valid pairs include (0,1),(0,3),(2,3); answer = (0,1)
def test6_nums : Array Int := #[1, 5, 1, 5]
def test6_target : Int := 6
def test6_Expected : (Nat × Nat) := (0, 1)

-- Test case 7: solution at the end of the array
-- nums = [1,2,3,4,4], target = 8, answer = (3,4)
def test7_nums : Array Int := #[1, 2, 3, 4, 4]
def test7_target : Int := 8
def test7_Expected : (Nat × Nat) := (3, 4)

-- Test case 8: minimal size with mixed signs
-- nums = [10,-10], target = 0, answer = (0,1)
def test8_nums : Array Int := #[10, -10]
def test8_target : Int := 0
def test8_Expected : (Nat × Nat) := (0, 1)

-- Test case 9: many duplicate values leading to many valid pairs
-- nums = [2,2,2,2], target = 4, answer = (0,1)
def test9_nums : Array Int := #[2, 2, 2, 2]
def test9_target : Int := 4
def test9_Expected : (Nat × Nat) := (0, 1)
end TestCases
