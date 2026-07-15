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
    FirstIndexWhere: determine the first index in an array where a predicate holds.

    Natural language breakdown:
    1. Inputs are an array `a : Array Int` and a predicate `P : Int → Bool`.
    2. The precondition states that at least one element of `a` satisfies `P`.
    3. The output `result : Nat` is an index into `a`.
    4. The returned index is in bounds: `result < a.size`.
    5. The element at index `result` satisfies the predicate: `P (a[result]!) = true`.
    6. All earlier indices do not satisfy the predicate: for all `j < result`, `P (a[j]!) = false`.
    7. Therefore `result` is the first (least) index where `P` holds.
-/

section Specs
-- Helper: `P` holds at index `i` (with bounds).
-- This is a Prop, even though `P` returns Bool.
def HoldsAt (a : Array Int) (P : Int → Bool) (i : Nat) : Prop :=
  i < a.size ∧ P (a[i]!) = true

-- Preconditions: there exists at least one index satisfying `P`.
def precondition (a : Array Int) (P : Int → Bool) : Prop :=
  ∃ i : Nat, HoldsAt a P i

-- Postconditions: `result` is the first index satisfying `P`.
def postcondition (a : Array Int) (P : Int → Bool) (result : Nat) : Prop :=
  result < a.size ∧
  P (a[result]!) = true ∧
  (∀ j : Nat, j < result → P (a[j]!) = false)
end Specs

section Impl
method FirstIndexWhere (a : Array Int) (P : Int → Bool)
  return (result : Nat)
  require precondition a P
  ensures postcondition a P result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical case (first satisfying element is in the middle)
-- Example predicate: fun x => x > 5
def test1_a : Array Int := #[1, 2, 6, 7]
def test1_P : Int → Bool := fun x => x > 5
def test1_Expected : Nat := 2

-- Test case 2: first element already satisfies
def test2_a : Array Int := #[10, 0, 1]
def test2_P : Int → Bool := fun x => x ≥ 10
def test2_Expected : Nat := 0

-- Test case 3: last element is the first satisfying element
def test3_a : Array Int := #[0, 1, 2, 3]
def test3_P : Int → Bool := fun x => x = 3
def test3_Expected : Nat := 3

-- Test case 4: singleton array (minimal size satisfying the precondition)
def test4_a : Array Int := #[42]
def test4_P : Int → Bool := fun x => x = 42
def test4_Expected : Nat := 0

-- Test case 5: includes negative numbers; predicate is "is negative"
def test5_a : Array Int := #[5, 0, -1, -2]
def test5_P : Int → Bool := fun x => x < 0
def test5_Expected : Nat := 2

-- Test case 6: multiple satisfying elements; must choose the first
-- First even number is at index 1 (value 2)
def test6_a : Array Int := #[1, 2, 3, 4, 5, 6]
def test6_P : Int → Bool := fun x => x % 2 = 0
def test6_Expected : Nat := 1

-- Test case 7: predicate always true; must return 0
def test7_a : Array Int := #[0, 0, 0]
def test7_P : Int → Bool := fun _ => true
def test7_Expected : Nat := 0

-- Test case 8: duplicates; first occurrence that satisfies must be selected
def test8_a : Array Int := #[-3, -3, 7, 7, 7]
def test8_P : Int → Bool := fun x => x = 7
def test8_Expected : Nat := 2

-- Test case 9: check boundary Int values -1,0,1; first satisfying at index 0
-- Predicate: x ≤ 0
def test9_a : Array Int := #[-1, 0, 1]
def test9_P : Int → Bool := fun x => x ≤ 0
def test9_Expected : Nat := 0

-- Recommend to validate: test1_Expected, test4_Expected, test9_Expected
end TestCases
