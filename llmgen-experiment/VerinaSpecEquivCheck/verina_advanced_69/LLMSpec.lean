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
    SearchInsertIndex: given a strictly increasing sorted list of distinct integers and a target integer,
    return the index of the target if it occurs, otherwise return the index where it can be inserted
    to maintain sorted order.
    Natural language breakdown:
    1. The input list xs is sorted in strictly increasing order and has no duplicates.
    2. The output result is a natural number index in the range [0, xs.length].
    3. All elements strictly before result are strictly less than target.
    4. All elements at indices result or later (if any) are greater than or equal to target.
    5. Therefore, inserting target at position result preserves sorted order, and if target exists in xs,
       then result is the index of its (unique) occurrence.
-/

section Specs
-- Helper predicate: xs is strictly increasing.
def StrictInc (xs : List Int) : Prop :=
  xs.Chain' (fun a b => a < b)

-- Lower-bound style characterization of the insertion point.
def precondition (xs : List Int) (target : Int) : Prop :=
  StrictInc xs

def postcondition (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result ≤ xs.length ∧
  (∀ (i : Nat), i < result → xs[i]! < target) ∧
  (∀ (i : Nat), result ≤ i → i < xs.length → target ≤ xs[i]!)
end Specs

section Impl
method SearchInsertIndex (xs : List Int) (target : Int)
  return (result : Nat)
  require precondition xs target
  ensures postcondition xs target result
  do
  -- Placeholder implementation only
  pure 0

end Impl

section TestCases
-- Test case 1: example-style mid insertion in a typical increasing list
-- xs = [-1, 0, 3, 5, 9, 12], target = 2, expected insertion index = 2
-- (since 0 < 2 ≤ 3)
def test1_xs : List Int := [-1, 0, 3, 5, 9, 12]
def test1_target : Int := 2
def test1_Expected : Nat := 2

-- Test case 2: target found at beginning
-- xs = [1, 3, 5], target = 1 -> index 0

def test2_xs : List Int := [1, 3, 5]
def test2_target : Int := 1
def test2_Expected : Nat := 0

-- Test case 3: target found in middle
-- xs = [1, 3, 5], target = 3 -> index 1

def test3_xs : List Int := [1, 3, 5]
def test3_target : Int := 3
def test3_Expected : Nat := 1

-- Test case 4: target greater than all elements (insert at end)
-- xs = [1, 3, 5], target = 7 -> index 3

def test4_xs : List Int := [1, 3, 5]
def test4_target : Int := 7
def test4_Expected : Nat := 3

-- Test case 5: empty list (only valid insertion index is 0)

def test5_xs : List Int := []
def test5_target : Int := 10
def test5_Expected : Nat := 0

-- Test case 6: singleton list, target smaller than element (insert at 0)

def test6_xs : List Int := [5]
def test6_target : Int := 4
def test6_Expected : Nat := 0

-- Test case 7: singleton list, target equal to element (found at 0)

def test7_xs : List Int := [5]
def test7_target : Int := 5
def test7_Expected : Nat := 0

-- Test case 8: singleton list, target larger than element (insert at 1)

def test8_xs : List Int := [5]
def test8_target : Int := 6
def test8_Expected : Nat := 1

-- Test case 9: negative values and insertion at the very front
-- xs = [-10, -3, 0, 4], target = -20 -> index 0

def test9_xs : List Int := [-10, -3, 0, 4]
def test9_target : Int := -20
def test9_Expected : Nat := 0

-- Test case 10: insertion between negatives
-- xs = [-10, -3, 0, 4], target = -5 -> index 1

def test10_xs : List Int := [-10, -3, 0, 4]
def test10_target : Int := -5
def test10_Expected : Nat := 1
end TestCases
