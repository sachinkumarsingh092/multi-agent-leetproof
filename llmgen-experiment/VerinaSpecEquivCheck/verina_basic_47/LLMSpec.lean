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
    ArrayIntSum: compute the sum of all elements of an array of integers.
    Natural language breakdown:
    1. The input is an array `a` whose elements are integers.
    2. The output is one integer `result`.
    3. `result` is the total obtained by adding every element of `a` exactly once.
    4. If `a` is empty, the sum is 0.
    5. The order of elements does not affect the sum (integer addition is commutative), but the
       specification is given by summing over all valid indices.
-/

section Specs
-- Helper definition: the mathematical sum of an array over its index range.
-- This is an observational spec (sum over indices), not an implementation algorithm.
def arrayIndexSum (a : Array Int) : Int :=
  (Finset.range a.size).sum (fun (i : Nat) => a[i]!)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Int) : Prop :=
  result = arrayIndexSum a
end Specs

section Impl
method ArrayIntSum (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: empty array
def test1_a : Array Int := #[]
def test1_Expected : Int := 0

-- Test case 2: singleton array (positive)
def test2_a : Array Int := #[ (5 : Int) ]
def test2_Expected : Int := 5

-- Test case 3: singleton array (negative)
def test3_a : Array Int := #[ (-7 : Int) ]
def test3_Expected : Int := -7

-- Test case 4: all zeros
def test4_a : Array Int := #[ (0 : Int), (0 : Int), (0 : Int) ]
def test4_Expected : Int := 0

-- Test case 5: mixed positive/negative
def test5_a : Array Int := #[ (1 : Int), (-2 : Int), (3 : Int), (-4 : Int) ]
def test5_Expected : Int := -2

-- Test case 6: typical small positives
def test6_a : Array Int := #[ (1 : Int), (2 : Int), (3 : Int), (4 : Int) ]
def test6_Expected : Int := 10

-- Test case 7: includes zeros and negatives
def test7_a : Array Int := #[ (0 : Int), (10 : Int), (0 : Int), (-10 : Int), (5 : Int) ]
def test7_Expected : Int := 5

-- Test case 8: larger magnitude values
def test8_a : Array Int := #[ (1000000 : Int), (-500000 : Int), (7 : Int) ]
def test8_Expected : Int := 500007

-- Test case 9: repeated values
def test9_a : Array Int := #[ (2 : Int), (2 : Int), (2 : Int), (2 : Int) ]
def test9_Expected : Int := 8
end TestCases
