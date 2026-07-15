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
    verina_basic_76: return the smaller (minimum) of two integers.

    Natural language breakdown:
    1. The input consists of two integers x and y.
    2. The output is an integer result.
    3. If x is less than or equal to y, the result must be x.
    4. If x is greater than y (equivalently y ≤ x and ¬ x ≤ y), the result must be y.
    5. The result is always one of the inputs.
    6. The result is less than or equal to both inputs.
-/

section Specs
-- No helper functions are required.

def precondition (x : Int) (y : Int) : Prop :=
  True

def postcondition (x : Int) (y : Int) (result : Int) : Prop :=
  -- result is a lower bound of x and y
  (result ≤ x) ∧
  (result ≤ y) ∧
  -- result must be one of the inputs
  (result = x ∨ result = y) ∧
  -- tie-breaking/characterization by the order
  (x ≤ y → result = x) ∧
  (y ≤ x → result = y)
end Specs

section Impl
method IntMin (x : Int) (y : Int)
  return (result : Int)
  require precondition x y
  ensures postcondition x y result
  do
    pure 0

end Impl

section TestCases
-- Test case 1: typical case where x < y
def test1_x : Int := 3
def test1_y : Int := 10
def test1_Expected : Int := 3

-- Test case 2: typical case where x > y
def test2_x : Int := 10
def test2_y : Int := 3
def test2_Expected : Int := 3

-- Test case 3: equal inputs
def test3_x : Int := 7
def test3_y : Int := 7
def test3_Expected : Int := 7

-- Test case 4: includes -1, 0, 1 edge coverage (x = -1, y = 0)
def test4_x : Int := -1
def test4_y : Int := 0
def test4_Expected : Int := -1

-- Test case 5: includes -1, 0, 1 edge coverage (x = 0, y = 1)
def test5_x : Int := 0
def test5_y : Int := 1
def test5_Expected : Int := 0

-- Test case 6: includes -1, 0, 1 edge coverage (x = 1, y = -1)
def test6_x : Int := 1
def test6_y : Int := -1
def test6_Expected : Int := -1

-- Test case 7: both negative
def test7_x : Int := -10
def test7_y : Int := -3
def test7_Expected : Int := -10

-- Test case 8: larger magnitude values
def test8_x : Int := 123456
def test8_y : Int := -999999
def test8_Expected : Int := -999999

-- Test case 9: boundary-like mix around zero
def test9_x : Int := 0
def test9_y : Int := -1
def test9_Expected : Int := -1
end TestCases
