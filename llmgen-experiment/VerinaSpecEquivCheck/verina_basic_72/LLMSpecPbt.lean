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
    AppendToArray: construct a new array by adding an extra integer to the end of an existing array.

    Natural language breakdown:
    1. Input consists of an array of integers a and an integer b.
    2. The output is an array of integers result.
    3. The output must contain all elements of a in the same order at the beginning.
    4. The last element of result must be b.
    5. Therefore, result has size a.size + 1.
    6. There are no special preconditions: the method must work for any a and any b.
-/

section Specs
-- No helper definitions are required.

def precondition (a : Array Int) (b : Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Int) (result : Array Int) : Prop :=
  result.size = a.size + 1 ∧
  (∀ (i : Nat), i < a.size → result[i]! = a[i]!) ∧
  result[a.size]! = b
end Specs

section Impl
method AppendToArray (a : Array Int) (b : Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure (#[] : Array Int)  -- placeholder body

prove_correct AppendToArray by sorry
end Impl

section TestCases
-- Test case 1: typical small array
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Int := 4
def test1_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 2: empty array (boundary)
def test2_a : Array Int := (#[] : Array Int)
def test2_b : Int := 7
def test2_Expected : Array Int := #[7]

-- Test case 3: singleton array (boundary)
def test3_a : Array Int := #[0]
def test3_b : Int := 0
def test3_Expected : Array Int := #[0, 0]

-- Test case 4: append negative number
def test4_a : Array Int := #[5, 6]
def test4_b : Int := (-3)
def test4_Expected : Array Int := #[5, 6, -3]

-- Test case 5: array with negative values
def test5_a : Array Int := #[-1, -2, -3]
def test5_b : Int := 10
def test5_Expected : Array Int := #[-1, -2, -3, 10]

-- Test case 6: append to longer array
def test6_a : Array Int := #[9, 8, 7, 6, 5]
def test6_b : Int := 1
def test6_Expected : Array Int := #[9, 8, 7, 6, 5, 1]

-- Test case 7: append a large magnitude integer
def test7_a : Array Int := #[42]
def test7_b : Int := 1000000000
def test7_Expected : Array Int := #[42, 1000000000]

-- Test case 8: append to array containing duplicates
def test8_a : Array Int := #[2, 2, 2]
def test8_b : Int := 2
def test8_Expected : Array Int := #[2, 2, 2, 2]

-- Test case 9: append to array containing both signs
def test9_a : Array Int := #[3, -4, 5, -6]
def test9_b : Int := (-7)
def test9_Expected : Array Int := #[3, -4, 5, -6, -7]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
