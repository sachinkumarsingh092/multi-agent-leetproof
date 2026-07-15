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
    HaveCommonElement: Check whether two arrays of integers share at least one element.
    Natural language breakdown:
    1. We are given two arrays `a` and `b` containing integers.
    2. The result should be true exactly when there exists an integer value that occurs in both arrays.
    3. If no integer appears in both arrays, the result should be false.
    4. Array order and multiplicity do not matter beyond existence of a shared value.
    5. Either array may be empty; in that case there is no shared element.
-/

section Specs
-- Helper predicate: there exists a value present in both arrays.
-- We use Array membership directly (no Array/List conversions in specs).
def hasCommon (a : Array Int) (b : Array Int) : Prop :=
  ∃ x : Int, x ∈ a ∧ x ∈ b

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  (result = true ↔ hasCommon a b) ∧
  (result = false ↔ ¬ hasCommon a b)
end Specs

section Impl
method HaveCommonElement (a : Array Int) (b : Array Int)
  return (result : Bool)
  require precondition a b
  ensures postcondition a b result
  do
  pure false

end Impl

section TestCases
-- Test case 1: typical case with a common element
-- Common element is 2.
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[5, 2, 8]
def test1_Expected : Bool := true

-- Test case 2: no common elements

def test2_a : Array Int := #[1, 2, 3]
def test2_b : Array Int := #[4, 5, 6]
def test2_Expected : Bool := false

-- Test case 3: both arrays empty

def test3_a : Array Int := #[]
def test3_b : Array Int := #[]
def test3_Expected : Bool := false

-- Test case 4: one empty, one non-empty

def test4_a : Array Int := #[]
def test4_b : Array Int := #[0]
def test4_Expected : Bool := false

-- Test case 5: singleton arrays with same element

def test5_a : Array Int := #[7]
def test5_b : Array Int := #[7]
def test5_Expected : Bool := true

-- Test case 6: singleton arrays with different elements

def test6_a : Array Int := #[7]
def test6_b : Array Int := #[8]
def test6_Expected : Bool := false

-- Test case 7: common negative element

def test7_a : Array Int := #[-1, 0, 2]
def test7_b : Array Int := #[3, -1]
def test7_Expected : Bool := true

-- Test case 8: duplicates present but still no overlap

def test8_a : Array Int := #[1, 1, 1]
def test8_b : Array Int := #[2, 2]
def test8_Expected : Bool := false

-- Test case 9: overlap with zero

def test9_a : Array Int := #[0, 10]
def test9_b : Array Int := #[0]
def test9_Expected : Bool := true
end TestCases
