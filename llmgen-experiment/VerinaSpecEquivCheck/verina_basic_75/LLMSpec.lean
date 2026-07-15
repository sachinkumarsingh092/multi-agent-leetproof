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
    ArrayMin: find the minimum element in a non-empty array of integers.

    Natural language breakdown:
    1. The input is an array of integers.
    2. The array is assumed to be non-empty.
    3. The output is an integer that is the minimum value occurring in the array.
    4. The returned value must be less than or equal to every element of the array.
    5. The returned value must be equal to at least one element of the array (it is attained).
-/

section Specs
-- Precondition: the array is non-empty.
-- We keep this decidable/computable by using `a.size > 0`.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: `result` is a minimum element of `a`.
-- 1) Lower bound: result ≤ every element in the array.
-- 2) Attainment: result equals some element in the array.
def postcondition (a : Array Int) (result : Int) : Prop :=
  (∀ (i : Nat), i < a.size → result ≤ a[i]!) ∧
  (∃ (i : Nat), i < a.size ∧ result = a[i]!)
end Specs

section Impl
method ArrayMin (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure (0 : Int)  -- placeholder body only

end Impl

section TestCases
-- Test case 1: typical mixed values
def test1_a : Array Int := #[3, -1, 2, 7]
def test1_Expected : Int := -1

-- Test case 2: singleton array (edge case)
def test2_a : Array Int := #[5]
def test2_Expected : Int := 5

-- Test case 3: contains zero and positives (must include 0 as valid Int value)
def test3_a : Array Int := #[0, 4, 2]
def test3_Expected : Int := 0

-- Test case 4: strictly increasing
def test4_a : Array Int := #[-3, -2, -1, 0, 1, 2]
def test4_Expected : Int := -3

-- Test case 5: strictly decreasing
def test5_a : Array Int := #[10, 9, 8, 7, 6]
def test5_Expected : Int := 6

-- Test case 6: all equal values
def test6_a : Array Int := #[4, 4, 4, 4]
def test6_Expected : Int := 4

-- Test case 7: duplicates with minimum repeated
def test7_a : Array Int := #[2, -5, 3, -5, 1]
def test7_Expected : Int := -5

-- Test case 8: includes both negative and positive extremes
def test8_a : Array Int := #[2147483647, -2147483648, 0, 42]
def test8_Expected : Int := -2147483648

-- Test case 9: minimum occurs at the end
def test9_a : Array Int := #[1, 2, 3, -10]
def test9_Expected : Int := -10
end TestCases
