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
    verina_basic_39: Rotate a list of integers to the right by a given number of positions.

    Natural language breakdown:
    1. Input is a list l : List Int and a rotation amount n : Nat.
    2. The output is a list result : List Int.
    3. The output list has the same length as the input list.
    4. If the input list is empty, the output is the empty list.
    5. If the input list is nonempty, elements are shifted to the right by n positions.
    6. Rotating right by n uses wrap-around: elements that move past the end reappear at the front.
    7. For a nonempty list, rotating by n and by n % l.length have the same effect.
    8. For every valid index i in the result (0 ≤ i < l.length), the element at i comes from
       index (i + l.length - (n % l.length)) % l.length in the original list.
-/

section Specs
-- Helper: source index in the original list for the element that ends up at position i
-- after rotating l to the right by n.
-- Intended to be used only when len > 0.
def rightRotateSrcIdx (len : Nat) (n : Nat) (i : Nat) : Nat :=
  (i + len - (n % len)) % len

def precondition (l : List Int) (n : Nat) : Prop :=
  True

def postcondition (l : List Int) (n : Nat) (result : List Int) : Prop :=
  result.length = l.length ∧
  (l.length = 0 → result = []) ∧
  (l.length > 0 →
    ∀ (i : Nat), i < l.length →
      result[i]! = l[rightRotateSrcIdx l.length n i]!)
end Specs

section Impl
method RotateRightListInt (l : List Int) (n : Nat)
  return (result : List Int)
  require precondition l n
  ensures postcondition l n result
  do
  -- Placeholder implementation only
  pure l

end Impl

section TestCases
-- Test case 1: empty list stays empty (special case)
def test1_l : List Int := []
def test1_n : Nat := 3
def test1_Expected : List Int := []

-- Test case 2: n = 0, list unchanged
def test2_l : List Int := [1, 2, 3]
def test2_n : Nat := 0
def test2_Expected : List Int := [1, 2, 3]

-- Test case 3: rotate right by 1
def test3_l : List Int := [1, 2, 3, 4]
def test3_n : Nat := 1
def test3_Expected : List Int := [4, 1, 2, 3]

-- Test case 4: rotate right by length (no change)
def test4_l : List Int := [10, 20, 30]
def test4_n : Nat := 3
def test4_Expected : List Int := [10, 20, 30]

-- Test case 5: rotate right by more than length (uses modulo)
def test5_l : List Int := [10, 20, 30]
def test5_n : Nat := 4
def test5_Expected : List Int := [30, 10, 20]

-- Test case 6: singleton list (always unchanged)
def test6_l : List Int := [42]
def test6_n : Nat := 7
def test6_Expected : List Int := [42]

-- Test case 7: list containing negative and non-negative integers
def test7_l : List Int := [-1, 0, 1]
def test7_n : Nat := 2
def test7_Expected : List Int := [0, 1, -1]

-- Test case 8: rotate right by 2 on even length
def test8_l : List Int := [1, 2, 3, 4, 5, 6]
def test8_n : Nat := 2
def test8_Expected : List Int := [5, 6, 1, 2, 3, 4]

-- Test case 9: two-element list, rotate by 1 swaps elements
def test9_l : List Int := [7, 8]
def test9_n : Nat := 1
def test9_Expected : List Int := [8, 7]

-- Recommend to validate: RotateRightListInt, precondition, postcondition
end TestCases
