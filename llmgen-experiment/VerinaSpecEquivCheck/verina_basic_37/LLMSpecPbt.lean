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
    FirstOccurrenceIndex: Locate the first occurrence index of a target integer in a sorted array.
    Natural language breakdown:
    1. Input is an array `arr : Array Int` that is sorted in non-decreasing order.
    2. Input also includes an integer `target : Int`.
    3. The output is an integer `result : Int`.
    4. If `target` does not occur in `arr`, then `result = -1`.
    5. If `target` occurs in `arr`, then `result` is the index (0-based) of the first occurrence of `target`.
    6. “First occurrence” means: at index `k`, `arr[k] = target`, and for every index `j < k`, `arr[j] ≠ target`.
    7. The input array is not modified by the method (arrays are immutable values; the postcondition only constrains `result`).
-/

section Specs
-- Array is sorted in non-decreasing order.
-- We phrase this using Nat indices and `arr[i]!` with explicit bounds.
def isSortedND (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: the input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedND arr

-- Postcondition:
-- Either the target is absent and we return -1,
-- or we return `Int.ofNat k` where `k` is the smallest index with `arr[k] = target`.
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ (i : Nat), i < arr.size → arr[i]! ≠ target)) ∨
  (∃ (k : Nat),
      k < arr.size ∧
      result = Int.ofNat k ∧
      arr[k]! = target ∧
      (∀ (j : Nat), j < k → arr[j]! ≠ target))
end Specs

section Impl
method FirstOccurrenceIndex (arr : Array Int) (target : Int)
  return (result : Int)
  require precondition arr target
  ensures postcondition arr target result
  do
    pure (-1)

prove_correct FirstOccurrenceIndex by sorry
end Impl

section TestCases
-- Test case 1: typical case with duplicates; first occurrence should be returned
-- arr = [-2, 0, 0, 0, 5], target = 0 => index 1

def test1_arr : Array Int := #[-2, 0, 0, 0, 5]
def test1_target : Int := 0
def test1_Expected : Int := 1

-- Test case 2: empty array; target absent

def test2_arr : Array Int := #[]
def test2_target : Int := 7
def test2_Expected : Int := (-1)

-- Test case 3: singleton array; target present at index 0

def test3_arr : Array Int := #[3]
def test3_target : Int := 3
def test3_Expected : Int := 0

-- Test case 4: singleton array; target absent

def test4_arr : Array Int := #[3]
def test4_target : Int := 2
def test4_Expected : Int := (-1)

-- Test case 5: all elements are the target; first occurrence is 0

def test5_arr : Array Int := #[4, 4, 4, 4]
def test5_target : Int := 4
def test5_Expected : Int := 0

-- Test case 6: target smaller than all elements; absent

def test6_arr : Array Int := #[1, 2, 3, 4]
def test6_target : Int := 0
def test6_Expected : Int := (-1)

-- Test case 7: target larger than all elements; absent

def test7_arr : Array Int := #[1, 2, 3, 4]
def test7_target : Int := 10
def test7_Expected : Int := (-1)

-- Test case 8: target present at the last index

def test8_arr : Array Int := #[-5, -1, 2, 9]
def test8_target : Int := 9
def test8_Expected : Int := 3

-- Test case 9: target present with negative values and duplicates; must pick first duplicate
-- arr = [-3, -3, -2, 0], target = -3 => index 0

def test9_arr : Array Int := #[-3, -3, -2, 0]
def test9_target : Int := (-3)
def test9_Expected : Int := 0
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_arr test9_target result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
