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
    LastOccurrenceSortedArray: Find the last occurrence index of an element in a sorted array of integers.
    Natural language breakdown:
    1. Input is an array `arr` of integers that is sorted in non-decreasing order.
    2. Input also includes an integer `elem`.
    3. If `elem` appears in `arr`, the result is the index of the last position where `arr[index] = elem`.
    4. If `elem` does not appear in `arr`, the result is -1.
    5. The array is not modified by the method.
-/

section Specs
-- Helper: sortedness in non-decreasing order (using Nat indices and `arr[i]!`).
def isSortedNondesc (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: element membership expressed via indices.
def contains (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: `k` is a last-occurrence index of `elem`.
def isLastOccurrenceIdx (arr : Array Int) (elem : Int) (k : Nat) : Prop :=
  k < arr.size ∧
  arr[k]! = elem ∧
  ∀ (j : Nat), k < j → j < arr.size → arr[j]! ≠ elem

-- Preconditions: the input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (elem : Int) : Prop :=
  isSortedNondesc arr

-- Postconditions: result is -1 iff `elem` is absent, otherwise result is the (unique) last index.
def postcondition (arr : Array Int) (elem : Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ (i : Nat), i < arr.size → arr[i]! ≠ elem)) ∨
  (∃ (k : Nat), result = Int.ofNat k ∧ isLastOccurrenceIdx arr elem k)
end Specs

section Impl
method LastOccurrenceSortedArray (arr : Array Int) (elem : Int)
  return (result : Int)
  require precondition arr elem
  ensures postcondition arr elem result
  do
    pure (-1)  -- placeholder

prove_correct LastOccurrenceSortedArray by sorry
end Impl

section TestCases
-- Test case 1: typical, multiple occurrences
-- arr = [1, 2, 2, 2, 3], elem = 2 => last index = 3

def test1_arr : Array Int := #[1, 2, 2, 2, 3]
def test1_elem : Int := 2
def test1_Expected : Int := 3

-- Test case 2: element absent in non-empty array
-- arr = [1, 2, 4, 5], elem = 3 => -1

def test2_arr : Array Int := #[1, 2, 4, 5]
def test2_elem : Int := 3
def test2_Expected : Int := (-1)

-- Test case 3: empty array (edge case)
-- arr = [], elem = 7 => -1

def test3_arr : Array Int := #[]
def test3_elem : Int := 7
def test3_Expected : Int := (-1)

-- Test case 4: singleton array where element is present (edge case)
-- arr = [5], elem = 5 => 0

def test4_arr : Array Int := #[5]
def test4_elem : Int := 5
def test4_Expected : Int := 0

-- Test case 5: singleton array where element is absent (edge case)
-- arr = [5], elem = 4 => -1

def test5_arr : Array Int := #[5]
def test5_elem : Int := 4
def test5_Expected : Int := (-1)

-- Test case 6: element occurs at the end, with duplicates at end
-- arr = [0, 1, 3, 3, 3], elem = 3 => 4

def test6_arr : Array Int := #[0, 1, 3, 3, 3]
def test6_elem : Int := 3
def test6_Expected : Int := 4

-- Test case 7: element is smaller than all entries
-- arr = [10, 11, 12], elem = 1 => -1

def test7_arr : Array Int := #[10, 11, 12]
def test7_elem : Int := 1
def test7_Expected : Int := (-1)

-- Test case 8: element is larger than all entries
-- arr = [-2, 0, 7], elem = 9 => -1

def test8_arr : Array Int := #[-2, 0, 7]
def test8_elem : Int := 9
def test8_Expected : Int := (-1)

-- Test case 9: negative numbers and duplicates
-- arr = [-5, -5, -1, 0], elem = -5 => last index = 1

def test9_arr : Array Int := #[-5, -5, -1, 0]
def test9_elem : Int := (-5)
def test9_Expected : Int := 1
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_arr test9_elem result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
