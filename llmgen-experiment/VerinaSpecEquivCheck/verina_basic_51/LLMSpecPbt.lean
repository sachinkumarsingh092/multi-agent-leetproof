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
    LowerBoundIndex: determine the insertion index for an integer key in a sorted array.
    Natural language breakdown:
    1. Input is an array `a` of integers sorted in non-decreasing order, and an integer `key`.
    2. The output is a natural number `result` interpreted as an index into the array.
    3. `result` must be between `0` and `a.size` (inclusive).
    4. Every element strictly before `result` is strictly less than `key`.
    5. Every element from `result` onward (within bounds) is greater than or equal to `key`.
    6. If `key` is larger than all elements, the correct insertion index is `a.size`.
    7. This is the first position where inserting `key` preserves the sorted order.
-/

section Specs
-- Array is sorted in non-decreasing order.
def isSortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- Lower-bound / insertion index property.
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNondecreasing a

def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  result ≤ a.size ∧
  (∀ (i : Nat), i < result → a[i]! < key) ∧
  (∀ (i : Nat), result ≤ i → i < a.size → key ≤ a[i]!)
end Specs

section Impl
method LowerBoundIndex (a : Array Int) (key : Int)
  return (result : Nat)
  require precondition a key
  ensures postcondition a key result
  do
  pure 0

prove_correct LowerBoundIndex by sorry
end Impl

section TestCases
-- Test case 1: empty array
def test1_a : Array Int := #[]
def test1_key : Int := 5
def test1_Expected : Nat := 0

-- Test case 2: singleton, key smaller than element
def test2_a : Array Int := #[10]
def test2_key : Int := 3
def test2_Expected : Nat := 0

-- Test case 3: singleton, key equal to element
def test3_a : Array Int := #[10]
def test3_key : Int := 10
def test3_Expected : Nat := 0

-- Test case 4: singleton, key larger than element
def test4_a : Array Int := #[10]
def test4_key : Int := 11
def test4_Expected : Nat := 1

-- Test case 5: typical increasing array, key inside range and not present
def test5_a : Array Int := #[1, 3, 5, 7]
def test5_key : Int := 4
def test5_Expected : Nat := 2

-- Test case 6: typical increasing array, key present (first occurrence position)
def test6_a : Array Int := #[1, 3, 5, 7]
def test6_key : Int := 5
def test6_Expected : Nat := 2

-- Test case 7: array with duplicates, key matches duplicated value
def test7_a : Array Int := #[1, 2, 2, 2, 4]
def test7_key : Int := 2
def test7_Expected : Nat := 1

-- Test case 8: array with duplicates, key between duplicate block and next value
def test8_a : Array Int := #[1, 2, 2, 2, 4]
def test8_key : Int := 3
def test8_Expected : Nat := 4

-- Test case 9: negative values, key within range
def test9_a : Array Int := #[-10, -5, 0, 3]
def test9_key : Int := -6
def test9_Expected : Nat := 1
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_key result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
