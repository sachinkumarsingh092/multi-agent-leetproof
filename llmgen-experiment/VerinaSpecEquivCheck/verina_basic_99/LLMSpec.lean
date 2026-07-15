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
    TripleInt: Compute three times the given integer.
    Natural language breakdown:
    1. The input is a single integer x.
    2. The output is an integer equal to three times x.
    3. The implementation may branch on whether x < 18 or x ≥ 18.
    4. Regardless of the branch taken, the returned value must equal 3 * x.
-/

section Specs
-- No helper functions are required: Int multiplication is provided by Mathlib/Lean.

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int) : Prop :=
  result = 3 * x
end Specs

section Impl
method TripleInt (x : Int)
  return (result : Int)
  require precondition x
  ensures postcondition x result
  do
    pure 0  -- placeholder body only

end Impl

section TestCases
-- Test case 1: x = 0 (required edge case)
def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: x = 1 (required edge case)
def test2_x : Int := 1
def test2_Expected : Int := 3

-- Test case 3: x = -1 (required edge case for Int)
def test3_x : Int := -1
def test3_Expected : Int := -3

-- Test case 4: x = 17 (just below the branch threshold 18)
def test4_x : Int := 17
def test4_Expected : Int := 51

-- Test case 5: x = 18 (at the branch threshold)
def test5_x : Int := 18
def test5_Expected : Int := 54

-- Test case 6: x = 19 (just above the branch threshold)
def test6_x : Int := 19
def test6_Expected : Int := 57

-- Test case 7: x = -18 (negative value near the magnitude of the threshold)
def test7_x : Int := -18
def test7_Expected : Int := -54

-- Test case 8: x = 123456 (larger positive)
def test8_x : Int := 123456
def test8_Expected : Int := 370368

-- Test case 9: x = -1000000 (larger negative)
def test9_x : Int := -1000000
def test9_Expected : Int := -3000000
end TestCases
