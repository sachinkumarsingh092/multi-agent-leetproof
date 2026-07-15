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
    MajorityElement: return the majority element from a list of integers.
    Natural language breakdown:
    1. The input is a list of integers `nums`.
    2. Let `n` be the length of `nums`.
    3. A value `m` is a majority element of `nums` iff it occurs in `nums` more than ⌊n/2⌋ times.
    4. The output `result` must be a majority element of `nums`.
    5. We assume a majority element always exists in the input.
    6. A majority element is unique: if two values each occur more than ⌊n/2⌋ times, then they are equal.
-/

section Specs
-- A predicate characterizing when a value is a majority element of a list.
-- We use `List.count` (with `BEq Int`) to count occurrences.
def IsMajority (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2

-- Precondition: a majority element exists.
-- Note: This implies `nums` is nonempty.
def precondition (nums : List Int) : Prop :=
  ∃ x : Int, IsMajority nums x

-- Postcondition: the result is a majority element, and it is the unique such value.
def postcondition (nums : List Int) (result : Int) : Prop :=
  IsMajority nums result ∧
  (∀ x : Int, IsMajority nums x → x = result)
end Specs

section Impl
method MajorityElement (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical case with a clear majority
-- nums = [2,2,1,2,3] has majority 2 (3 out of 5)
def test1_nums : List Int := [2, 2, 1, 2, 3]
def test1_Expected : Int := 2

-- Test case 2: singleton list (edge case); the only element is the majority
def test2_nums : List Int := [7]
def test2_Expected : Int := 7

-- Test case 3: all equal elements
def test3_nums : List Int := [5, 5, 5, 5]
def test3_Expected : Int := 5

-- Test case 4: even length; majority must be strictly more than n/2
-- nums length 6, n/2 = 3, so need count ≥ 4
def test4_nums : List Int := [1, 1, 1, 1, 2, 3]
def test4_Expected : Int := 1

-- Test case 5: includes negative numbers; majority is -1
def test5_nums : List Int := [-1, -1, -1, 0, 1]
def test5_Expected : Int := -1

-- Test case 6: majority is 0 (includes boundary-like value 0)
def test6_nums : List Int := [0, 0, 0, 1, 2]
def test6_Expected : Int := 0

-- Test case 7: majority appears in the tail
def test7_nums : List Int := [3, 1, 3, 2, 3, 3, 4]
def test7_Expected : Int := 3

-- Test case 8: minimal nontrivial size 2; one element must appear twice to be a majority
def test8_nums : List Int := [9, 9]
def test8_Expected : Int := 9

-- Test case 9: larger odd length with scattered majority
def test9_nums : List Int := [10, 20, 10, 30, 10, 40, 10, 50, 10]
def test9_Expected : Int := 10

-- Recommend to validate: singleton, even/odd length, negative majority
end TestCases
