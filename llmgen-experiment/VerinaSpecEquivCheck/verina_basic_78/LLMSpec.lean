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
    SumAndDifference: Given two integers x and y, compute a pair consisting of their sum and their difference.

    Natural language breakdown:
    1. The input consists of two integers x and y.
    2. The output is a pair (s, d) of integers.
    3. The first component s equals x + y.
    4. The second component d equals x - y.
    5. There are no constraints on x or y beyond being valid integers.
-/

section Specs
-- No helper functions are required: we use Int addition/subtraction and product projections.

def precondition (x : Int) (y : Int) : Prop :=
  True

def postcondition (x : Int) (y : Int) (result : (Int × Int)) : Prop :=
  result.1 = x + y ∧ result.2 = x - y
end Specs

section Impl
method SumAndDifference (x : Int) (y : Int)
  return (result : (Int × Int))
  require precondition x y
  ensures postcondition x y result
  do
    pure (0, 0)  -- placeholder

end Impl

section TestCases
-- Test case 1: typical positive inputs
-- x = 7, y = 3 => (10, 4)
def test1_x : Int := 7
def test1_y : Int := 3
def test1_Expected : (Int × Int) := (10, 4)

-- Test case 2: both zero (boundary)
def test2_x : Int := 0
def test2_y : Int := 0
def test2_Expected : (Int × Int) := (0, 0)

-- Test case 3: x = 0, y = 1 (boundary includes 1)
def test3_x : Int := 0
def test3_y : Int := 1
def test3_Expected : (Int × Int) := (1, -1)

-- Test case 4: x = 1, y = 0 (boundary)
def test4_x : Int := 1
def test4_y : Int := 0
def test4_Expected : (Int × Int) := (1, 1)

-- Test case 5: include -1, 0, 1 (explicitly)
def test5_x : Int := -1
def test5_y : Int := 1
def test5_Expected : (Int × Int) := (0, -2)

-- Test case 6: both negative
-- x = -5, y = -8 => (-13, 3)
def test6_x : Int := -5
def test6_y : Int := -8
def test6_Expected : (Int × Int) := (-13, 3)

-- Test case 7: mixed signs
-- x = 10, y = -4 => (6, 14)
def test7_x : Int := 10
def test7_y : Int := -4
def test7_Expected : (Int × Int) := (6, 14)

-- Test case 8: larger magnitude values
-- x = 123456, y = 654321 => (777777, -530865)
def test8_x : Int := 123456
def test8_y : Int := 654321
def test8_Expected : (Int × Int) := (777777, -530865)

-- Test case 9: subtraction resulting in zero
-- x = 42, y = 42 => (84, 0)
def test9_x : Int := 42
def test9_y : Int := 42
def test9_Expected : (Int × Int) := (84, 0)
end TestCases
