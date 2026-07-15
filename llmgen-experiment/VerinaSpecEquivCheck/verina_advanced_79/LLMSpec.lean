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
    TwoSum: find indices of two list elements whose values sum to a target.

    Natural language breakdown:
    1. Inputs are a list of integers `nums` and an integer `target`.
    2. A valid answer is a pair of indices `(i, j)` such that `i < j`.
    3. Both indices must be within the bounds of the list: `j < nums.length` (and hence `i < nums.length`).
    4. The elements at those indices must sum to the target: `nums[i] + nums[j] = target`.
    5. If no valid pair of indices exists, the result is `none`.
    6. If one or more valid pairs exist, the result is `some (i, j)` where `(i, j)` is the lexicographically first
       valid pair: it has the smallest `i`, and among those with that `i`, the smallest `j`.
-/

section Specs
-- Lexicographic (non-strict) order on pairs of natural numbers.
-- `a ≤lex b` iff `a.1 < b.1` or (`a.1 = b.1` and `a.2 ≤ b.2`).
def lexLE (a : Nat × Nat) (b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

-- A pair of indices is valid for TwoSum if it is in-bounds, ordered i<j, and sums to target.
def ValidPair (nums : List Int) (target : Int) (p : Nat × Nat) : Prop :=
  p.1 < p.2 ∧ p.2 < nums.length ∧ nums[p.1]! + nums[p.2]! = target

-- No preconditions: all lists and targets are allowed.
def precondition (nums : List Int) (target : Int) : Prop :=
  True

def postcondition (nums : List Int) (target : Int) (result : Option (Nat × Nat)) : Prop :=
  match result with
  | none =>
      -- No valid pair exists.
      ∀ (i : Nat) (j : Nat), i < j → j < nums.length → nums[i]! + nums[j]! ≠ target
  | some p =>
      -- Returned pair is valid and lexicographically minimal among all valid pairs.
      ValidPair nums target p ∧
      (∀ (q : Nat × Nat), ValidPair nums target q → lexLE p q)
end Specs

section Impl
method TwoSum (nums : List Int) (target : Int)
  return (result : Option (Nat × Nat))
  require precondition nums target
  ensures postcondition nums target result
  do
    pure none

end Impl

section TestCases
-- Test case 1: classic example
def test1_nums : List Int := [2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Option (Nat × Nat) := some (0, 1)

-- Test case 2: empty list (degenerate)
def test2_nums : List Int := []
def test2_target : Int := 0
def test2_Expected : Option (Nat × Nat) := none

-- Test case 3: singleton list (degenerate)
def test3_nums : List Int := [42]
def test3_target : Int := 42
def test3_Expected : Option (Nat × Nat) := none

-- Test case 4: two elements that match
def test4_nums : List Int := [3, 4]
def test4_target : Int := 7
def test4_Expected : Option (Nat × Nat) := some (0, 1)

-- Test case 5: multiple solutions; choose lexicographically first (smallest i)
def test5_nums : List Int := [1, 2, 3, 4]
def test5_target : Int := 5
-- valid pairs: (0,3) and (1,2); lexicographically first is (0,3)
def test5_Expected : Option (Nat × Nat) := some (0, 3)

-- Test case 6: multiple solutions; choose smallest j among same i
def test6_nums : List Int := [0, 0, 0]
def test6_target : Int := 0
-- valid pairs include (0,1), (0,2), (1,2); lexicographically first is (0,1)
def test6_Expected : Option (Nat × Nat) := some (0, 1)

-- Test case 7: includes negative numbers
def test7_nums : List Int := [-1, -2, -3, -4, -5]
def test7_target : Int := -8
-- valid pairs: (2,4) only; -3 + -5 = -8
def test7_Expected : Option (Nat × Nat) := some (2, 4)

-- Test case 8: no solution with duplicates present
def test8_nums : List Int := [1, 1, 1, 1]
def test8_target : Int := 3
def test8_Expected : Option (Nat × Nat) := none
end TestCases
