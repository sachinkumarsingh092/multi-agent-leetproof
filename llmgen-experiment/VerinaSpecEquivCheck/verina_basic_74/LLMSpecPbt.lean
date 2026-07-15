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
    ArrayMaxInt: Identify the maximum value in a non-empty array of integers.
    Natural language breakdown:
    1. The input is an array `a` of integers.
    2. The array is assumed to be non-empty (its size is at least 1).
    3. The output is an integer `result`.
    4. `result` must be greater than or equal to every element of the array.
    5. `result` must be equal to one of the elements of the array.
    6. If the array is empty, behavior is unspecified; we rule this out with a precondition.
-/

section Specs
-- Helper predicate: `val` occurs in the array at some valid index.
-- Using an index-based formulation keeps the spec decidable and avoids list conversions.
def occursIn (a : Array Int) (val : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = val

-- Preconditions
-- The array must be non-empty.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result is a maximum element: (1) it is an element of the array,
-- and (2) all elements are ≤ result.
def postcondition (a : Array Int) (result : Int) : Prop :=
  occursIn a result ∧
  (∀ (i : Nat), i < a.size → a[i]! ≤ result)
end Specs

section Impl
method ArrayMaxInt (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure (0 : Int)  -- placeholder

prove_correct ArrayMaxInt by sorry
end Impl

section TestCases
-- Test case 1: typical mixed values
-- max([3,1,2]) = 3

def test1_a : Array Int := #[3, 1, 2]
def test1_Expected : Int := 3

-- Test case 2: singleton array (edge case)

def test2_a : Array Int := #[42]
def test2_Expected : Int := 42

-- Test case 3: all negative values

def test3_a : Array Int := #[-5, -1, -3]
def test3_Expected : Int := -1

-- Test case 4: contains -1, 0, 1 (boundary-ish values for Int)

def test4_a : Array Int := #[-1, 0, 1]
def test4_Expected : Int := 1

-- Test case 5: duplicates of the maximum

def test5_a : Array Int := #[2, 7, 7, 1]
def test5_Expected : Int := 7

-- Test case 6: strictly increasing

def test6_a : Array Int := #[1, 2, 3, 4, 5]
def test6_Expected : Int := 5

-- Test case 7: strictly decreasing

def test7_a : Array Int := #[5, 4, 3, 2, 1]
def test7_Expected : Int := 5

-- Test case 8: includes zero and negatives, maximum at the end

def test8_a : Array Int := #[0, -10, -2, 9]
def test8_Expected : Int := 9

-- Test case 9: all elements equal

def test9_a : Array Int := #[6, 6, 6]
def test9_Expected : Int := 6
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
