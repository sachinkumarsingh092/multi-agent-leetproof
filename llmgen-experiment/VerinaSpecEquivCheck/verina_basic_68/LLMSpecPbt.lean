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
    ArrayFirstIndex: Find the index of the first occurrence of a target integer in an array.

    Natural language breakdown:
    1. Input is an array `a` of integers and a target integer `e`.
    2. If `e` occurs in `a`, the output is the smallest index `i` such that `i < a.size` and `a[i]! = e`.
    3. If `e` does not occur in `a`, the output is `a.size`.
    4. The output is always a natural number that is either a valid index into the array or exactly the array size.
-/

section Specs
-- `result` is the first index where `a[result]! = e`, or `a.size` if `e` does not occur.

def precondition (a : Array Int) (e : Int) : Prop :=
  True

def postcondition (a : Array Int) (e : Int) (result : Nat) : Prop :=
  result ≤ a.size ∧
  ((result < a.size ∧ a[result]! = e ∧ (∀ j : Nat, j < result → a[j]! ≠ e)) ∨
   (result = a.size ∧ (∀ j : Nat, j < a.size → a[j]! ≠ e)))
end Specs

section Impl
method ArrayFirstIndex (a : Array Int) (e : Int)
  return (result : Nat)
  require precondition a e
  ensures postcondition a e result
  do
  pure 0

prove_correct ArrayFirstIndex by sorry
end Impl

section TestCases
-- Test case 1: example-style case (multiple occurrences; take the first)
def test1_a : Array Int := #[3, 1, 4, 1, 5]
def test1_e : Int := 1
def test1_Expected : Nat := 1

-- Test case 2: empty array, element absent => result = size = 0
def test2_a : Array Int := #[]
def test2_e : Int := 7
def test2_Expected : Nat := 0

-- Test case 3: singleton array, element present at index 0
def test3_a : Array Int := #[42]
def test3_e : Int := 42
def test3_Expected : Nat := 0

-- Test case 4: singleton array, element absent => result = size = 1
def test4_a : Array Int := #[42]
def test4_e : Int := 0
def test4_Expected : Nat := 1

-- Test case 5: element present at the last index
def test5_a : Array Int := #[10, 20, 30]
def test5_e : Int := 30
def test5_Expected : Nat := 2

-- Test case 6: element absent in a non-empty array => result = size
def test6_a : Array Int := #[10, 20, 30]
def test6_e : Int := 25
def test6_Expected : Nat := 3

-- Test case 7: repeated values; ensure first occurrence is returned
def test7_a : Array Int := #[5, 5, 5, 5]
def test7_e : Int := 5
def test7_Expected : Nat := 0

-- Test case 8: includes negative numbers; find negative target
def test8_a : Array Int := #[-3, -2, -1, 0, 1]
def test8_e : Int := -1
def test8_Expected : Nat := 2

-- Test case 9: negative target not present => return size
def test9_a : Array Int := #[-3, -2, -1, 0, 1]
def test9_e : Int := -4
def test9_Expected : Nat := 5
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_e result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
