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
    ReverseArray: reverse an array of integers.
    Natural language breakdown:
    1. Input is an array of integers (may be empty, singleton, or larger).
    2. Output is an array of integers.
    3. Output has the same size as the input.
    4. For each valid index i in the input (i < a.size), the output at index i equals
       the input at index (a.size - 1 - i).
    5. There are no preconditions; the method should handle any array.
-/

section Specs
-- No helper functions are required for this specification.

def precondition (a : Array Int) : Prop :=
  True

-- The postcondition is purely relational:
-- it characterizes the output by size preservation and index-wise reverse correspondence.
-- Note: we use Nat subtraction (a.size - 1 - i). When i < a.size, this denotes the
-- intended mirror index; Array indexing with `!` is total, so the property is decidable
-- and simple to state.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ (i : Nat), i < a.size → result[i]! = a[(a.size - 1 - i)]!
end Specs

section Impl
method ReverseArray (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
    -- Placeholder body only
    pure a.reverse

end Impl

section TestCases
-- Test case 1: empty array
-- (No example was provided in the prompt; use a boundary case first.)
def test1_a : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: singleton

def test2_a : Array Int := #[42]
def test2_Expected : Array Int := #[42]

-- Test case 3: two elements

def test3_a : Array Int := #[1, 2]
def test3_Expected : Array Int := #[2, 1]

-- Test case 4: three elements

def test4_a : Array Int := #[1, 2, 3]
def test4_Expected : Array Int := #[3, 2, 1]

-- Test case 5: includes negative numbers

def test5_a : Array Int := #[-1, 0, 7]
def test5_Expected : Array Int := #[7, 0, -1]

-- Test case 6: duplicates

def test6_a : Array Int := #[5, 5, 5, 5]
def test6_Expected : Array Int := #[5, 5, 5, 5]

-- Test case 7: mixed values and length 5

def test7_a : Array Int := #[10, -3, 4, 0, 9]
def test7_Expected : Array Int := #[9, 0, 4, -3, 10]

-- Test case 8: longer array

def test8_a : Array Int := #[1, 2, 3, 4, 5, 6]
def test8_Expected : Array Int := #[6, 5, 4, 3, 2, 1]

-- Test case 9: contains Int min/max-like magnitudes (within literal range)

def test9_a : Array Int := #[2147483647, -2147483648, 13]
def test9_Expected : Array Int := #[13, -2147483648, 2147483647]
end TestCases
