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
    ListToArray: Convert a list of integers into an array with the same elements in the same order.
    Natural language breakdown:
    1. The input is a list `xs` of integers.
    2. The output is an array `result` of integers.
    3. The output array must have size equal to the length of `xs`.
    4. For every valid index `i` with `i < xs.length`, the element at index `i` in the output array equals the element at index `i` in the input list.
    5. There are no additional preconditions; the method must work for any list.
-/

section Specs
-- No helper functions are required.

def precondition (xs : List Int) : Prop :=
  True

def postcondition (xs : List Int) (result : Array Int) : Prop :=
  result.size = xs.length ∧
  ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!
end Specs

section Impl
method ListToArray (xs : List Int)
  return (result : Array Int)
  require precondition xs
  ensures postcondition xs result
  do
    pure xs.toArray

prove_correct ListToArray by sorry
end Impl

section TestCases
-- Test case 1: typical mixed values
def test1_xs : List Int := [3, -1, 4, 0]
def test1_Expected : Array Int := #[3, -1, 4, 0]

-- Test case 2: empty list
def test2_xs : List Int := []
def test2_Expected : Array Int := #[]

-- Test case 3: singleton list (edge case)
def test3_xs : List Int := [7]
def test3_Expected : Array Int := #[7]

-- Test case 4: contains 0 and 1 explicitly
def test4_xs : List Int := [0, 1, 0, 1]
def test4_Expected : Array Int := #[0, 1, 0, 1]

-- Test case 5: all negative values
def test5_xs : List Int := [-5, -4, -3]
def test5_Expected : Array Int := #[-5, -4, -3]

-- Test case 6: already increasing sequence
def test6_xs : List Int := [1, 2, 3, 4, 5]
def test6_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 7: duplicates and larger magnitude values
def test7_xs : List Int := [1000000, -1000000, 1000000]
def test7_Expected : Array Int := #[1000000, -1000000, 1000000]

-- Test case 8: longer list to exercise indexing across many positions
def test8_xs : List Int := [9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def test8_Expected : Array Int := #[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Array Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_xs result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
