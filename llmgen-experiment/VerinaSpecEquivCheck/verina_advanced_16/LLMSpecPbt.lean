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
    InsertionSortIntList: Sort a list of integers in ascending order.

    Natural language breakdown:
    1. The input is a single list of integers xs.
    2. The output is a list of integers result.
    3. The output list is sorted in nondecreasing (ascending) order with respect to Int.≤.
    4. The output list contains exactly the same elements as the input list, counting multiplicity.
    5. Equivalently, the output list is a permutation of the input list.
    6. Empty lists and singleton lists are valid inputs.
    7. Example: input [3, 1, 4, 2] yields output [1, 2, 3, 4].
-/

section Specs
def precondition (xs : List Int) : Prop :=
  True

def postcondition (xs : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ List.Perm xs result
end Specs

section Impl
method InsertionSortIntList (xs : List Int)
  return (result : List Int)
  require precondition xs
  ensures postcondition xs result
  do
  -- Placeholder implementation only
  pure []

prove_correct InsertionSortIntList by sorry
end Impl

section TestCases
-- Test case 1: example from problem statement
-- Input:  [3, 1, 4, 2]
-- Output: [1, 2, 3, 4]
def test1_xs : List Int := [3, 1, 4, 2]
def test1_Expected : List Int := [1, 2, 3, 4]

-- Test case 2: empty list
def test2_xs : List Int := []
def test2_Expected : List Int := []

-- Test case 3: singleton list
def test3_xs : List Int := [7]
def test3_Expected : List Int := [7]

-- Test case 4: already sorted ascending
def test4_xs : List Int := [1, 2, 3, 4, 5]
def test4_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 5: reverse sorted
def test5_xs : List Int := [5, 4, 3, 2, 1]
def test5_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 6: contains duplicates
def test6_xs : List Int := [2, 1, 2, 1, 2]
def test6_Expected : List Int := [1, 1, 2, 2, 2]

-- Test case 7: includes negative values
-- Includes -1, 0, 1 coverage across suite (here we use -3,-2,-1,0,2)
def test7_xs : List Int := [-1, -3, 0, 2, -2]
def test7_Expected : List Int := [-3, -2, -1, 0, 2]

-- Test case 8: all elements equal
def test8_xs : List Int := [4, 4, 4, 4]
def test8_Expected : List Int := [4, 4, 4, 4]

-- Test case 9: mixed magnitudes
def test9_xs : List Int := [100, -100, 50, 0, -1, 1]
def test9_Expected : List Int := [-100, -1, 0, 1, 50, 100]

-- Recommend to validate: sortedness, permutation, edge cases
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : List Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_xs result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
