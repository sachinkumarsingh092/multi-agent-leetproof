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
    ElemwiseProduct: Compute the element-wise product of two integer arrays.
    Natural language breakdown:
    1. The inputs are two arrays `a` and `b` of integers.
    2. The intended result is an array of integers whose length matches the input arrays.
    3. For each valid index i, the result at i equals the product of the inputs at i.
    4. If one array were shorter, a missing element would be treated as 0 during multiplication.
    5. For this specification, we assume the arrays have equal length; thus no index is missing.
-/

section Specs
-- Helper: the value to use for a missing element (matches the problem statement).
-- This is not needed under the equal-length precondition, but documents the intended default.
def missingDefault : Int := 0

def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < result.size → result[i]! = a[i]! * b[i]!)
end Specs

section Impl
method ElemwiseProduct (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]  -- placeholder

end Impl

section TestCases
-- Test case 1: typical small arrays
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Array Int := #[4, 10, 18]

-- Test case 2: both arrays empty
def test2_a : Array Int := #[]
def test2_b : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: singleton arrays
def test3_a : Array Int := #[7]
def test3_b : Array Int := #[8]
def test3_Expected : Array Int := #[56]

-- Test case 4: zeros in inputs
def test4_a : Array Int := #[0, 2, 0]
def test4_b : Array Int := #[5, 0, 9]
def test4_Expected : Array Int := #[0, 0, 0]

-- Test case 5: negative values
def test5_a : Array Int := #[-1, 2, -3]
def test5_b : Array Int := #[4, -5, -6]
def test5_Expected : Array Int := #[-4, -10, 18]

-- Test case 6: mixed signs and a trailing zero
def test6_a : Array Int := #[10, -2, 3, 0]
def test6_b : Array Int := #[-3, -4, 0, 7]
def test6_Expected : Array Int := #[-30, 8, 0, 0]

-- Test case 7: larger magnitude values
def test7_a : Array Int := #[100000, -100000]
def test7_b : Array Int := #[-2, -3]
def test7_Expected : Array Int := #[-200000, 300000]

-- Test case 8: repeated values
def test8_a : Array Int := #[2, 2, 2, 2]
def test8_b : Array Int := #[3, 3, 3, 3]
def test8_Expected : Array Int := #[6, 6, 6, 6]

-- Test case 9: includes 1 and -1 factors
def test9_a : Array Int := #[1, -1, 1, -1]
def test9_b : Array Int := #[9, 9, -9, -9]
def test9_Expected : Array Int := #[9, -9, -9, 9]
end TestCases
