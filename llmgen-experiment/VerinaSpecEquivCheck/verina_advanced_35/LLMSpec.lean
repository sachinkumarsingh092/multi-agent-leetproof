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
    MajorityElement: Find the majority element in a list of integers.
    Natural language breakdown:
    1. Input is a list of integers `nums`.
    2. The input list is nonempty.
    3. For a value `m`, its number of occurrences in `nums` is `nums.count m`.
    4. A value `m` is a majority element of `nums` if it appears strictly more than ⌊(nums.length) / 2⌋ times.
    5. It is guaranteed that at least one majority element exists in the input.
    6. The function returns the (unique) value that satisfies the majority-element property.
-/

section Specs
-- Helper predicate: `m` is a majority element of `nums`.
-- `List.count` counts occurrences using `BEq` on `Int`.
def IsMajority (nums : List Int) (m : Int) : Prop :=
  nums.count m > nums.length / 2

-- Preconditions: the list is nonempty and has a majority element.
def precondition (nums : List Int) : Prop :=
  nums.length ≥ 1 ∧ ∃ m : Int, IsMajority nums m

-- Postcondition: result is a majority element, and any majority element must equal result.
def postcondition (nums : List Int) (result : Int) : Prop :=
  IsMajority nums result ∧ (∀ x : Int, IsMajority nums x → x = result)
end Specs

section Impl
method MajorityElement (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0  -- placeholder

end Impl

section TestCases
-- Test case 1: singleton list (degenerate nonempty case)
def test1_nums : List Int := [7]
def test1_Expected : Int := 7

-- Test case 2: two elements, majority is the repeated element
def test2_nums : List Int := [2, 2]
def test2_Expected : Int := 2

-- Test case 3: odd length, clear majority
def test3_nums : List Int := [3, 1, 3, 3, 2]
def test3_Expected : Int := 3

-- Test case 4: includes 0, majority is 0
def test4_nums : List Int := [0, 1, 0, 2, 0]
def test4_Expected : Int := 0

-- Test case 5: includes -1, majority is -1
def test5_nums : List Int := [-1, 0, -1, 1, -1, 2, -1]
def test5_Expected : Int := -1

-- Test case 6: even length, majority barely over half
def test6_nums : List Int := [5, 5, 5, 2, 3, 5]
def test6_Expected : Int := 5

-- Test case 7: majority element appears many times, with varied noise
def test7_nums : List Int := [10, 4, 10, 10, 6, 10, 7, 10, 10]
def test7_Expected : Int := 10

-- Test case 8: majority element is negative and list contains -1, 0, 1 values
def test8_nums : List Int := [-2, -2, -2, -1, 0, 1, -2]
def test8_Expected : Int := -2

-- Recommend to validate: test1_nums, test5_nums, test6_nums
end TestCases
