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
    ArrayElementwiseMod: Compute the element-wise integer modulo between two arrays.
    Natural language breakdown:
    1. We are given two arrays of integers `a` and `b`.
    2. The arrays must have the same length.
    3. Every divisor element in `b` must be non-zero.
    4. The result is a new array of integers with the same length as the inputs.
    5. For every valid index `i`, the result at position `i` equals `a[i] % b[i]`.
    6. The `%` operator is Lean's integer Euclidean remainder (`Int.emod`).
    7. The empty-array case is allowed; it yields an empty result.
-/

section Specs
-- Preconditions
-- "Non-null" is not meaningful in Lean; arrays are always values.

def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧
  (∀ (i : Nat), i < b.size → b[i]! ≠ 0)

-- Postconditions

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = a[i]! % b[i]!)
end Specs

section Impl
method ArrayElementwiseMod (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]

end Impl

section TestCases
-- Test case 1: typical small positive numbers
def test1_a : Array Int := #[10, 11, 12]
def test1_b : Array Int := #[3, 5, 6]
def test1_Expected : Array Int := #[1, 1, 0]

-- Test case 2: empty arrays (edge case; vacuously satisfies divisor-nonzero condition)
def test2_a : Array Int := #[]
def test2_b : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: singleton arrays
def test3_a : Array Int := #[7]
def test3_b : Array Int := #[2]
def test3_Expected : Array Int := #[1]

-- Test case 4: includes 0 in dividend
def test4_a : Array Int := #[0, 5, 0]
def test4_b : Array Int := #[7, 2, 1]
def test4_Expected : Array Int := #[0, 1, 0]

-- Test case 5: negative dividends (Euclidean remainder is nonnegative when divisor is nonzero)
def test5_a : Array Int := #[-7, -12, -1]
def test5_b : Array Int := #[3, 7, 2]
def test5_Expected : Array Int := #[2, 2, 1]

-- Test case 6: negative divisors
def test6_a : Array Int := #[7, 12, -12]
def test6_b : Array Int := #[-3, -7, -7]
def test6_Expected : Array Int := #[1, 5, 2]

-- Test case 7: mixed signs, larger values
def test7_a : Array Int := #[12345, -12345, 99999]
def test7_b : Array Int := #[97, 97, -100]
def test7_Expected : Array Int := #[26, 71, 99]

-- Test case 8: divisors are 1 and -1 (remainder should be 0)
def test8_a : Array Int := #[42, -42, 0, 1, -1]
def test8_b : Array Int := #[1, 1, -1, -1, -1]
def test8_Expected : Array Int := #[0, 0, 0, 0, 0]
end TestCases
