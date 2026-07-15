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
    IsEvenInt: Determine whether a given integer is even.

    Natural language breakdown:
    1. The input is an integer n.
    2. The output is a Boolean.
    3. The output should be true exactly when n is even.
    4. The output should be false exactly when n is not even (i.e., odd).
    5. There are no preconditions: the method must accept any integer.
-/

section Specs
-- No helper functions are required: Mathlib provides the predicate `Even n : Prop` for integers.

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ Even n) ∧
  (result = false ↔ ¬ Even n)
end Specs

section Impl
method IsEvenInt (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true  -- placeholder body

end Impl

section TestCases
-- Test case 1: boundary even integer 0
def test1_n : Int := 0
def test1_Expected : Bool := true

-- Test case 2: boundary odd integer 1
def test2_n : Int := 1
def test2_Expected : Bool := false

-- Test case 3: boundary odd integer -1
def test3_n : Int := (-1)
def test3_Expected : Bool := false

-- Test case 4: small positive even integer
def test4_n : Int := 2
def test4_Expected : Bool := true

-- Test case 5: small negative even integer
def test5_n : Int := (-2)
def test5_Expected : Bool := true

-- Test case 6: small positive odd integer
def test6_n : Int := 3
def test6_Expected : Bool := false

-- Test case 7: larger positive even integer
def test7_n : Int := 100
def test7_Expected : Bool := true

-- Test case 8: larger negative odd integer
def test8_n : Int := (-101)
def test8_Expected : Bool := false
end TestCases
