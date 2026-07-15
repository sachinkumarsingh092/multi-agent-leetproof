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
    ConcatArrays: Concatenate two arrays of integers by appending the second array to the end of the first.
    Natural language breakdown:
    1. The inputs are two arrays of integers, called a and b.
    2. The output is a new array of integers.
    3. The output length equals a.size + b.size.
    4. For every index i in the range 0 ≤ i < a.size, the output at index i equals a[i]!
    5. For every index j in the range 0 ≤ j < b.size, the output at index a.size + j equals b[j]!
    6. No additional preconditions are required.
-/

section Specs
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size + b.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = a[i]!) ∧
  (∀ (j : Nat), j < b.size → result[a.size + j]! = b[j]!)
end Specs

section Impl
method ConcatArrays (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure (a ++ b)  -- placeholder

end Impl

section TestCases
-- Test case 1: both arrays non-empty
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5]
def test1_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 2: a is empty
def test2_a : Array Int := #[]
def test2_b : Array Int := #[7, 8]
def test2_Expected : Array Int := #[7, 8]

-- Test case 3: b is empty
def test3_a : Array Int := #[9, 10]
def test3_b : Array Int := #[]
def test3_Expected : Array Int := #[9, 10]

-- Test case 4: both empty
def test4_a : Array Int := #[]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: singleton arrays
def test5_a : Array Int := #[42]
def test5_b : Array Int := #[100]
def test5_Expected : Array Int := #[42, 100]

-- Test case 6: negatives and zeros
def test6_a : Array Int := #[0, -1, -2]
def test6_b : Array Int := #[-3, 0]
def test6_Expected : Array Int := #[0, -1, -2, -3, 0]

-- Test case 7: larger second array
def test7_a : Array Int := #[5]
def test7_b : Array Int := #[6, 7, 8, 9]
def test7_Expected : Array Int := #[5, 6, 7, 8, 9]

-- Test case 8: repeated values
def test8_a : Array Int := #[1, 1, 1]
def test8_b : Array Int := #[1, 1]
def test8_Expected : Array Int := #[1, 1, 1, 1, 1]

-- Test case 9: mixture of small and large magnitude ints
def test9_a : Array Int := #[2147483647]
def test9_b : Array Int := #[-2147483648, 0]
def test9_Expected : Array Int := #[2147483647, -2147483648, 0]
end TestCases
