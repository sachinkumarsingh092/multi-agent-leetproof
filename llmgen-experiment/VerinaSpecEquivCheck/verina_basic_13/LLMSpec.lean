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
    CubeArrayElements: Replace every element of an integer array with its cube
    Natural language breakdown:
    1. Input is an array `a` of integers; it may be empty or non-empty.
    2. Output is an array `result` of integers.
    3. The output array has the same length as the input array.
    4. For every valid index `i` in the array, `result[i]` equals `a[i] * a[i] * a[i]`.
    5. There are no additional preconditions; the method must work for all integer arrays.
-/

section Specs
-- Helper: integer cube
def cubeInt (x : Int) : Int := x * x * x

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = cubeInt (a[i]!))
end Specs

section Impl
method CubeArrayElements (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure (#[])

end Impl

section TestCases
-- Test case 1: empty array
def test1_a : Array Int := #[]
def test1_Expected : Array Int := #[]

-- Test case 2: singleton zero
def test2_a : Array Int := #[0]
def test2_Expected : Array Int := #[0]

-- Test case 3: singleton one
def test3_a : Array Int := #[1]
def test3_Expected : Array Int := #[1]

-- Test case 4: singleton negative one
def test4_a : Array Int := #[-1]
def test4_Expected : Array Int := #[-1]

-- Test case 5: small mixed positives
def test5_a : Array Int := #[2, 3, 4]
def test5_Expected : Array Int := #[8, 27, 64]

-- Test case 6: mixed signs including zero
def test6_a : Array Int := #[-2, 0, 5]
def test6_Expected : Array Int := #[-8, 0, 125]

-- Test case 7: repeated elements
def test7_a : Array Int := #[3, 3, -3]
def test7_Expected : Array Int := #[27, 27, -27]

-- Test case 8: larger magnitude values
def test8_a : Array Int := #[10, -10]
def test8_Expected : Array Int := #[1000, -1000]

-- Test case 9: longer array with varied values
def test9_a : Array Int := #[-4, -1, 0, 1, 2]
def test9_Expected : Array Int := #[-64, -1, 0, 1, 8]
end TestCases
