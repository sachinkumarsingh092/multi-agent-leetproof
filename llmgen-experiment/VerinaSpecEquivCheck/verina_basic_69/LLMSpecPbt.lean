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
    FirstIndexOf: Determine the index of the first occurrence of a specified integer within an array.
    Natural language breakdown:
    1. Inputs are an array `a` of integers and a target integer `e`.
    2. It is assumed (precondition) that `e` occurs in `a` at least once.
    3. The output is a natural number `result` representing an index into `a`.
    4. The element at `result` is equal to `e`.
    5. Every index strictly smaller than `result` contains an element different from `e`.
    6. Therefore `result` is the smallest (first) index where `e` occurs.
-/

section Specs
-- `e` must occur in `a` at some in-bounds index.
def precondition (a : Array Int) (e : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = e

-- `result` is an in-bounds index of the first occurrence of `e`.
def postcondition (a : Array Int) (e : Int) (result : Nat) : Prop :=
  result < a.size ∧
  a[result]! = e ∧
  (∀ j : Nat, j < a.size → j < result → a[j]! ≠ e)
end Specs

section Impl
method FirstIndexOf (a : Array Int) (e : Int)
  return (result : Nat)
  require precondition a e
  ensures postcondition a e result
  do
  pure 0

prove_correct FirstIndexOf by sorry
end Impl

section TestCases
-- Test case 1: target appears multiple times; first occurrence in the middle
-- a = [5, 7, 7, 9], e = 7 => result = 1

def test1_a : Array Int := #[5, 7, 7, 9]
def test1_e : Int := 7
def test1_Expected : Nat := 1

-- Test case 2: target is at index 0 (boundary)

def test2_a : Array Int := #[3, 4, 5]
def test2_e : Int := 3
def test2_Expected : Nat := 0

-- Test case 3: target is at the last index

def test3_a : Array Int := #[10, 20, 30, 40]
def test3_e : Int := 40
def test3_Expected : Nat := 3

-- Test case 4: singleton array (degenerate but valid)

def test4_a : Array Int := #[42]
def test4_e : Int := 42
def test4_Expected : Nat := 0

-- Test case 5: includes negative numbers; target negative appears once

def test5_a : Array Int := #[-5, -4, -3, -2]
def test5_e : Int := -3
def test5_Expected : Nat := 2

-- Test case 6: many repeats; first occurrence later, not at 0

def test6_a : Array Int := #[1, 2, 2, 2, 2]
def test6_e : Int := 2
def test6_Expected : Nat := 1

-- Test case 7: repeated zeros; first occurrence at 0

def test7_a : Array Int := #[0, 0, 1, 0]
def test7_e : Int := 0
def test7_Expected : Nat := 0

-- Test case 8: larger array; target occurs twice, first near end

def test8_a : Array Int := #[8, 6, 7, 6, 5, 3, 0, 9]
def test8_e : Int := 9
def test8_Expected : Nat := 7

-- Test case 9: target appears after a long prefix without it

def test9_a : Array Int := #[11, 12, 13, 14, 15, 16, 17]
def test9_e : Int := 16
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
