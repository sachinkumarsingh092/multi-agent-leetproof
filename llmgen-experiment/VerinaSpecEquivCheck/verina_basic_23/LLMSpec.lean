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
    ArrayMaxMinDifference: Compute the difference between the maximum and minimum values in an array of integers.
    Natural language breakdown:
    1. The input is an array of integers.
    2. The array is assumed to be non-empty.
    3. A maximum value is an element of the array that is greater than or equal to every element in the array.
    4. A minimum value is an element of the array that is less than or equal to every element in the array.
    5. The output is the integer difference (maximum value) - (minimum value).
    6. For a singleton array, the maximum and minimum are the same element, so the result is 0.
-/

section Specs
-- Helper predicates describing when a value occurs in an array.
def occursIn (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

-- Upper/lower bound properties over all indices of the array.
def isUpperBound (a : Array Int) (v : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≤ v

def isLowerBound (a : Array Int) (v : Int) : Prop :=
  ∀ (i : Nat), i < a.size → v ≤ a[i]!

-- Characterization of maximum/minimum values (as elements + bound properties).
def isMaxValue (a : Array Int) (v : Int) : Prop :=
  occursIn a v ∧ isUpperBound a v

def isMinValue (a : Array Int) (v : Int) : Prop :=
  occursIn a v ∧ isLowerBound a v

-- Preconditions
-- The array must be non-empty.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result equals (max - min) for some max and min values of the array.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (maxV : Int) (minV : Int),
    isMaxValue a maxV ∧
    isMinValue a minV ∧
    result = maxV - minV
end Specs

section Impl
method ArrayMaxMinDifference (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical mixed values
def test1_a : Array Int := #[3, 1, 4, 2]
def test1_Expected : Int := 3

-- Test case 2: singleton array (edge case)
def test2_a : Array Int := #[5]
def test2_Expected : Int := 0

-- Test case 3: all equal values
def test3_a : Array Int := #[7, 7, 7]
def test3_Expected : Int := 0

-- Test case 4: includes negatives and positives
def test4_a : Array Int := #[-10, 0, 10]
def test4_Expected : Int := 20

-- Test case 5: all negative values
def test5_a : Array Int := #[-3, -7, -1, -4]
def test5_Expected : Int := 6

-- Test case 6: already increasing
def test6_a : Array Int := #[1, 2, 3, 4, 5]
def test6_Expected : Int := 4

-- Test case 7: already decreasing
def test7_a : Array Int := #[5, 4, 3, 2, 1]
def test7_Expected : Int := 4

-- Test case 8: contains duplicates of max and min
def test8_a : Array Int := #[2, 9, 2, 9, 5]
def test8_Expected : Int := 7

-- Test case 9: contains zero and negative minimum
def test9_a : Array Int := #[0, -1, 0, -1]
def test9_Expected : Int := 1
end TestCases
