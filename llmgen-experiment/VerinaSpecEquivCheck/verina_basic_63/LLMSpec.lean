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
    HasCloseFloatPair: Decide whether a list of floating-point numbers contains two distinct elements
    whose absolute difference is less than a given non-negative threshold.

    Natural language breakdown:
    1. Inputs are a list of floating-point numbers `numbers` and a floating-point number `threshold`.
    2. The list elements are assumed to be valid floating-point values (not NaN and not infinite).
    3. The threshold is assumed to be a valid floating-point value and non-negative.
    4. We consider pairs of elements at two different indices i and j (i ≠ j).
    5. A pair is considered "close" if Float.abs (numbers[i] - numbers[j]) < threshold.
    6. The output is true iff there exists at least one close pair.
    7. The output is false iff no close pair exists.
-/

section Specs
-- A Float value is considered valid if it is neither NaN nor infinite.
-- This matches the problem statement assumption and is kept decidable via boolean tests.
def FloatValid (x : Float) : Prop :=
  (x.isNaN = false) ∧ (x.isInf = false)

-- There exists a close pair of distinct indices in the list.
def HasClosePair (numbers : List Float) (threshold : Float) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < numbers.length ∧
    j < numbers.length ∧
    i ≠ j ∧
    Float.abs (numbers[i]! - numbers[j]!) < threshold

-- Preconditions
-- 1) All list elements are valid floats.
-- 2) The threshold is a valid float and is non-negative.
def precondition (numbers : List Float) (threshold : Float) : Prop :=
  (∀ (i : Nat), i < numbers.length → FloatValid (numbers[i]!)) ∧
  FloatValid threshold ∧
  (0.0 ≤ threshold)

-- Postcondition
-- The result is true iff a close pair exists.
def postcondition (numbers : List Float) (threshold : Float) (result : Bool) : Prop :=
  (result = true ↔ HasClosePair numbers threshold)
end Specs

section Impl
method HasCloseFloatPair (numbers : List Float) (threshold : Float)
  return (result : Bool)
  require precondition numbers threshold
  ensures postcondition numbers threshold result
  do
  -- placeholder implementation
  pure false

end Impl

section TestCases
-- Test case 1: empty list (no pair exists)
def test1_numbers : List Float := []
def test1_threshold : Float := 0.1
def test1_Expected : Bool := false

-- Test case 2: singleton list (no pair exists)
def test2_numbers : List Float := [3.14]
def test2_threshold : Float := 1.0
def test2_Expected : Bool := false

-- Test case 3: two elements with difference strictly less than threshold
-- |1.0 - 1.05| = 0.05 < 0.1
def test3_numbers : List Float := [1.0, 1.05]
def test3_threshold : Float := 0.1
def test3_Expected : Bool := true

-- Test case 4: two elements with difference equal to threshold (strict inequality fails)
-- |1.0 - 1.1| = 0.1 is not < 0.1
def test4_numbers : List Float := [1.0, 1.1]
def test4_threshold : Float := 0.1
def test4_Expected : Bool := false

-- Test case 5: duplicates with positive threshold (difference 0 < threshold)
def test5_numbers : List Float := [2.0, 2.0]
def test5_threshold : Float := 0.0001
def test5_Expected : Bool := true

-- Test case 6: duplicates with zero threshold (strict inequality fails: 0 < 0 is false)
def test6_numbers : List Float := [2.0, 2.0, 5.0]
def test6_threshold : Float := 0.0
def test6_Expected : Bool := false

-- Test case 7: close pair exists but not adjacent in the list
-- close pair: 10.0 and 10.001 with threshold 0.01
def test7_numbers : List Float := [0.0, 10.0, 100.0, 10.001]
def test7_threshold : Float := 0.01
def test7_Expected : Bool := true

-- Test case 8: negative values with a close pair
-- |-1.0 - (-1.0005)| = 0.0005 < 0.001
def test8_numbers : List Float := [-1.0, -1.0005, 7.0]
def test8_threshold : Float := 0.001
def test8_Expected : Bool := true

-- Test case 9: many elements, all distances >= threshold
-- (adjacent differences are 1.0, so with threshold 0.5 there is no close pair)
def test9_numbers : List Float := [0.0, 1.0, 2.0, 3.0, 4.0]
def test9_threshold : Float := 0.5
def test9_Expected : Bool := false

-- Recommend to validate: empty/singleton lists, strictness at equality, duplicates, and non-adjacent close pairs
end TestCases
