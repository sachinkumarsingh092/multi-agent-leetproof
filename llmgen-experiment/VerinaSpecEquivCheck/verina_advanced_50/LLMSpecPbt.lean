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
    MergeSortedUnique: Merge two sorted arrays of natural numbers into one sorted array without duplicates.
    Natural language breakdown:
    1. Inputs are two arrays of natural numbers a1 and a2.
    2. The task is ill-defined unless both input arrays are sorted in nondecreasing order.
    3. The output is a new array containing every value that appears in either input array.
    4. Each value must appear in the output once and only once (set-like union semantics).
    5. The output array itself must be sorted in nondecreasing order.
-/

section Specs
-- Helper: element membership in an array, expressed via index-based access.
-- (Avoids Array/List conversions in specifications.)
def inArray (arr : Array Nat) (x : Nat) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: sortedness for arrays (nondecreasing).
def isSorted (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! ≤ arr[i + 1]!

-- Helper: no duplicates in an array (index-based extensional nodup).
def nodupArray (arr : Array Nat) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < arr.size → j < arr.size → arr[i]! = arr[j]! → i = j

-- Preconditions: both arrays are sorted (nondecreasing). Behavior is unspecified otherwise.
def precondition (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  isSorted a1 ∧ isSorted a2

-- Postconditions:
-- 1. result is sorted
-- 2. result has no duplicates
-- 3. membership in result is exactly union of memberships of a1 and a2
-- Together these characterize the unique sorted duplicate-free representation of the union.
def postcondition (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  isSorted result ∧
  nodupArray result ∧
  (∀ (x : Nat), inArray result x ↔ (inArray a1 x ∨ inArray a2 x))
end Specs

section Impl
method MergeSortedUnique (a1 : Array Nat) (a2 : Array Nat)
  return (result : Array Nat)
  require precondition a1 a2
  ensures postcondition a1 a2 result
  do
  pure #[]  -- placeholder body

prove_correct MergeSortedUnique by sorry
end Impl

section TestCases
-- Test case 1: typical overlap
-- a1 = [1,3,5], a2 = [2,3,4,6] => union sorted unique = [1,2,3,4,5,6]
def test1_a1 : Array Nat := #[1, 3, 5]
def test1_a2 : Array Nat := #[2, 3, 4, 6]
def test1_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

-- Test case 2: both empty
-- [] ∪ [] = []
def test2_a1 : Array Nat := #[]
def test2_a2 : Array Nat := #[]
def test2_Expected : Array Nat := #[]

-- Test case 3: first empty
-- [] ∪ [0,1,2] = [0,1,2]
def test3_a1 : Array Nat := #[]
def test3_a2 : Array Nat := #[0, 1, 2]
def test3_Expected : Array Nat := #[0, 1, 2]

-- Test case 4: second empty
-- [0] ∪ [] = [0]
def test4_a1 : Array Nat := #[0]
def test4_a2 : Array Nat := #[]
def test4_Expected : Array Nat := #[0]

-- Test case 5: duplicates within each array and across arrays
-- [1,1,2,2] ∪ [2,2,3,3] = [1,2,3]
def test5_a1 : Array Nat := #[1, 1, 2, 2]
def test5_a2 : Array Nat := #[2, 2, 3, 3]
def test5_Expected : Array Nat := #[1, 2, 3]

-- Test case 6: disjoint ranges
-- [0,1,2] ∪ [5,6] = [0,1,2,5,6]
def test6_a1 : Array Nat := #[0, 1, 2]
def test6_a2 : Array Nat := #[5, 6]
def test6_Expected : Array Nat := #[0, 1, 2, 5, 6]

-- Test case 7: one array is subset of the other (with duplicates)
-- [1,2,3,4] ∪ [2,2,3] = [1,2,3,4]
def test7_a1 : Array Nat := #[1, 2, 3, 4]
def test7_a2 : Array Nat := #[2, 2, 3]
def test7_Expected : Array Nat := #[1, 2, 3, 4]

-- Test case 8: many zeros and small numbers
-- [0,0,0,1] ∪ [0,2] = [0,1,2]
def test8_a1 : Array Nat := #[0, 0, 0, 1]
def test8_a2 : Array Nat := #[0, 2]
def test8_Expected : Array Nat := #[0, 1, 2]

-- Test case 9: singleton arrays with same element
-- [7] ∪ [7] = [7]
def test9_a1 : Array Nat := #[7]
def test9_a2 : Array Nat := #[7]
def test9_Expected : Array Nat := #[7]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a1 test9_a2 result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
