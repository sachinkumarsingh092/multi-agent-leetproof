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
    MultiplyTwoIntegers: Multiply two integers and return their product.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must equal the mathematical product of a and b.
    4. The specification must work for positive, zero, and negative integers.
-/

section Specs
-- No helper functions are needed: Int multiplication is provided by `HMul.hMul` as `a * b`.

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result = a * b
end Specs

section Impl
method MultiplyTwoIntegers (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical positive numbers
def test1_a : Int := 6
def test1_b : Int := 7
def test1_Expected : Int := 42

-- Test case 2: multiplication by zero (left)
def test2_a : Int := 0
def test2_b : Int := 123
def test2_Expected : Int := 0

-- Test case 3: multiplication by zero (right)
def test3_a : Int := -999
def test3_b : Int := 0
def test3_Expected : Int := 0

-- Test case 4: negative times positive
def test4_a : Int := -6
def test4_b : Int := 7
def test4_Expected : Int := -42

-- Test case 5: positive times negative
def test5_a : Int := 6
def test5_b : Int := -7
def test5_Expected : Int := -42

-- Test case 6: negative times negative
def test6_a : Int := -6
def test6_b : Int := -7
def test6_Expected : Int := 42

-- Test case 7: boundary/edge values around -1, 0, 1
def test7_a : Int := -1
def test7_b : Int := 1
def test7_Expected : Int := -1

-- Test case 8: both ones
def test8_a : Int := 1
def test8_b : Int := 1
def test8_Expected : Int := 1

-- Test case 9: larger magnitude values
def test9_a : Int := 12345
def test9_b : Int := -6789
def test9_Expected : Int := -83810205
end TestCases
