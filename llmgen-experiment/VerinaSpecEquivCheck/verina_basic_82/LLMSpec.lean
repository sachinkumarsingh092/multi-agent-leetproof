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
    DropFirstElement: Produce a new array that excludes the first element of a non-empty array.
    Natural language breakdown:
    1. The input is an array `a` of integers.
    2. The input array is assumed to be non-empty.
    3. The output is an array `result` that contains all elements of `a` except the first one.
    4. Therefore, `result` has size `a.size - 1`.
    5. For every valid index `i` into `result`, `result[i]!` equals `a[i+1]!`.
-/

section Specs
def precondition (a : Array Int) : Prop :=
  a.size > 0

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size - 1 ∧
  ∀ (i : Nat), i < result.size → result[i]! = a[i + 1]!
end Specs

section Impl
method DropFirstElement (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure (#[] : Array Int)  -- placeholder

end Impl

section TestCases
-- Test case 1: singleton array; dropping first yields empty
def test1_a : Array Int := #[7]
def test1_Expected : Array Int := #[]

-- Test case 2: two elements
def test2_a : Array Int := #[1, 2]
def test2_Expected : Array Int := #[2]

-- Test case 3: three elements
def test3_a : Array Int := #[10, 20, 30]
def test3_Expected : Array Int := #[20, 30]

-- Test case 4: includes negative values
def test4_a : Array Int := #[-1, 0, 1]
def test4_Expected : Array Int := #[0, 1]

-- Test case 5: all equal values
def test5_a : Array Int := #[5, 5, 5, 5]
def test5_Expected : Array Int := #[5, 5, 5]

-- Test case 6: larger array
def test6_a : Array Int := #[3, 1, 4, 1, 5, 9]
def test6_Expected : Array Int := #[1, 4, 1, 5, 9]

-- Test case 7: first element is 0
def test7_a : Array Int := #[0, 2, 4, 6]
def test7_Expected : Array Int := #[2, 4, 6]

-- Test case 8: mix of positive and negative, length 2
def test8_a : Array Int := #[42, -7]
def test8_Expected : Array Int := #[-7]

-- Recommend to validate: singleton input, minimal length=2, negative/zero/positive values
end TestCases
