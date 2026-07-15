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
    OnlyOneDistinctElement: Determine whether an array of integers contains only one distinct element.
    Natural language breakdown:
    1. The input is an array `a` of integers.
    2. If the array is empty, the result should be true.
    3. If the array is non-empty, the result should be true exactly when every element equals the first element.
    4. If there exist two indices in the array whose elements are different, the result should be false.
    5. The method returns a Boolean that reflects this property.
-/

section Specs
-- Helper predicate: the array has at most one distinct value.
-- We make the empty-array case explicit to avoid out-of-bounds access to a[0]!. 
def allSame (a : Array Int) : Prop :=
  a.size = 0 ∨ (0 < a.size ∧ ∀ (i : Nat), i < a.size → a[i]! = a[0]!)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ allSame a) ∧
  (result = false ↔ ¬ allSame a)
end Specs

section Impl
method OnlyOneDistinctElement (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure true

end Impl

section TestCases
-- Test case 1: empty array -> true
def test1_a : Array Int := #[]
def test1_Expected : Bool := true

-- Test case 2: singleton array -> true
def test2_a : Array Int := #[5]
def test2_Expected : Bool := true

-- Test case 3: all elements equal (positive) -> true
def test3_a : Array Int := #[7, 7, 7, 7]
def test3_Expected : Bool := true

-- Test case 4: two elements different -> false
def test4_a : Array Int := #[1, 2]
def test4_Expected : Bool := false

-- Test case 5: difference occurs later -> false
def test5_a : Array Int := #[3, 3, 3, 4, 3]
def test5_Expected : Bool := false

-- Test case 6: all elements equal (negative) -> true
def test6_a : Array Int := #[-2, -2, -2]
def test6_Expected : Bool := true

-- Test case 7: mix of negative and zero with a difference -> false
def test7_a : Array Int := #[0, 0, -1, 0]
def test7_Expected : Bool := false

-- Test case 8: all elements equal (zero) -> true
def test8_a : Array Int := #[0, 0, 0]
def test8_Expected : Bool := true

-- Test case 9: large magnitude integers with a difference -> false
def test9_a : Array Int := #[1000000, 1000000, 1000001]
def test9_Expected : Bool := false
end TestCases
