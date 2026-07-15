import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    IsSortedNonDecreasing: Check whether an array of integers is sorted in non-decreasing order.

    Natural language breakdown:
    1. The input is an array of integers; it may be empty or have any length.
    2. The output is a Boolean.
    3. The result is true exactly when the array is sorted in non-decreasing order.
    4. “Sorted in non-decreasing order” means every adjacent pair is ordered:
       for every index i, if i+1 is within bounds then a[i] ≤ a[i+1].
    5. If the result is false, then the array is not sorted in non-decreasing order.
       Equivalently, it is not the case that all adjacent pairs are ordered.
    6. Empty and singleton arrays are sorted (the adjacent condition holds vacuously).
-/

section Specs
-- Adjacent non-decreasing property.
-- Uses Nat indices and the safe index operator a[i]! guarded by bounds.
def SortedAdjacent (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

def precondition (a : Array Int) : Prop :=
  True

-- The result is fully characterized:
-- result is true iff the adjacent sortedness predicate holds,
-- and result is false iff the adjacent sortedness predicate does not hold.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ SortedAdjacent a) ∧
  (result = false ↔ ¬ SortedAdjacent a)
end Specs

section Impl
method IsSortedNonDecreasing (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure true

prove_correct IsSortedNonDecreasing by sorry
end Impl

section TestCases
-- Test case 1: empty array (edge case: vacuously sorted)
def test1_a : Array Int := #[]
def test1_Expected : Bool := true

-- Test case 2: singleton array (edge case)
def test2_a : Array Int := #[7]
def test2_Expected : Bool := true

-- Test case 3: two elements already sorted
def test3_a : Array Int := #[1, 2]
def test3_Expected : Bool := true

-- Test case 4: two elements unsorted (single adjacent inversion)
def test4_a : Array Int := #[2, 1]
def test4_Expected : Bool := false

-- Test case 5: already sorted with duplicates allowed
def test5_a : Array Int := #[1, 1, 2, 2, 2]
def test5_Expected : Bool := true

-- Test case 6: unsorted in the middle
def test6_a : Array Int := #[1, 3, 2, 4]
def test6_Expected : Bool := false

-- Test case 7: strictly increasing with negative values
def test7_a : Array Int := #[-3, -1, 0, 5]
def test7_Expected : Bool := true

-- Test case 8: decreasing sequence (many inversions)
def test8_a : Array Int := #[5, 4, 3, 2, 1]
def test8_Expected : Bool := false

-- Test case 9: all equal values (including 0)
def test9_a : Array Int := #[0, 0, 0, 0]
def test9_Expected : Bool := true

-- Recommend to validate: empty/singleton vacuity, duplicates allowed, negative values
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Bool) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
