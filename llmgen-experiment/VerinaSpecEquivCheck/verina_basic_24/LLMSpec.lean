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
    DiffFirstEvenOdd: compute the difference between the first even number and the first odd number in an array of integers.
    Natural language breakdown:
    1. The input is an array `a` of integers.
    2. The array is non-empty.
    3. The array contains at least one even element and at least one odd element.
    4. "First even" means the leftmost element of the array that is even.
    5. "First odd" means the leftmost element of the array that is odd.
    6. The method returns (first even element) minus (first odd element).
    7. The method conceptually scans the array from left to right, but the specification is property-based.
-/

section Specs
-- Helper predicates for parity using Int modulo.
-- With divisor 2 > 0, Int.mod returns 0 or 1.
def isEven (n : Int) : Prop := n % 2 = 0

def isOdd (n : Int) : Prop := n % 2 = 1

-- `i` is the index of the first even element in `a`.
def isFirstEvenIdx (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧
  isEven (a[i]!) ∧
  ∀ (j : Nat), j < i → ¬ isEven (a[j]!)

-- `i` is the index of the first odd element in `a`.
def isFirstOddIdx (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧
  isOdd (a[i]!) ∧
  ∀ (j : Nat), j < i → ¬ isOdd (a[j]!)

-- Precondition: array is non-empty and contains at least one even and at least one odd.
def precondition (a : Array Int) : Prop :=
  a.size > 0 ∧
  (∃ (i : Nat), i < a.size ∧ isEven (a[i]!)) ∧
  (∃ (i : Nat), i < a.size ∧ isOdd (a[i]!))

-- Postcondition: result equals (first even) - (first odd).
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (iEven : Nat) (iOdd : Nat),
    isFirstEvenIdx a iEven ∧
    isFirstOddIdx a iOdd ∧
    result = a[iEven]! - a[iOdd]!
end Specs

section Impl
method DiffFirstEvenOdd (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical mixed array
def test1_a : Array Int := #[2, 3, 4]
def test1_Expected : Int := -1

-- Test case 2: minimum-size valid array (odd then even)
def test2_a : Array Int := #[1, 2]
def test2_Expected : Int := 1

-- Test case 3: includes 0 and 1
def test3_a : Array Int := #[0, 1]
def test3_Expected : Int := -1

-- Test case 4: includes negative odd
def test4_a : Array Int := #[-1, 4, 6]
def test4_Expected : Int := 5

-- Test case 5: first even at index 0, first odd later
def test5_a : Array Int := #[8, 10, 3, 5]
def test5_Expected : Int := 5

-- Test case 6: first odd at index 0, first even later
def test6_a : Array Int := #[7, 9, 2, 4]
def test6_Expected : Int := -5

-- Test case 7: many odds before first even
def test7_a : Array Int := #[1, 3, 5, 2]
def test7_Expected : Int := 1

-- Test case 8: many evens before first odd
def test8_a : Array Int := #[2, 4, 6, 1]
def test8_Expected : Int := 1

-- Test case 9: mix with 0 and negative values
def test9_a : Array Int := #[0, -3, -2]
def test9_Expected : Int := 3
end TestCases
