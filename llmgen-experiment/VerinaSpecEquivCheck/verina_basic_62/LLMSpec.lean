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
    FirstIndexOfKey: Find the first occurrence index of a given integer key in an integer array.
    Natural language breakdown:
    1. Input is an array `a` of integers and an integer `key`.
    2. If `key` does not occur in `a`, the function returns -1.
    3. Otherwise, the function returns an integer index `result` such that:
       a. `result` denotes a valid array index (0 ≤ result and result.toNat < a.size).
       b. The element at that index equals the key: a[result.toNat]! = key.
       c. The index is the first occurrence: for every j < result.toNat, a[j]! ≠ key.
    4. The array may be empty or non-empty; there are no additional input restrictions.
-/

section Specs
-- Helper: key is absent from the array
def keyAbsent (a : Array Int) (key : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≠ key

-- Helper: key is present in the array
def keyPresent (a : Array Int) (key : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = key

-- No preconditions
def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  (result = (-1) ∧ keyAbsent a key) ∨
  (result ≠ (-1) ∧
    0 ≤ result ∧
    (Int.toNat result) < a.size ∧
    a[(Int.toNat result)]! = key ∧
    (∀ (j : Nat), j < (Int.toNat result) → a[j]! ≠ key))
end Specs

section Impl
method FirstIndexOfKey (a : Array Int) (key : Int)
  return (result : Int)
  require precondition a key
  ensures postcondition a key result
  do
  pure (-1)  -- placeholder

end Impl

section TestCases
-- Test case 1: key present multiple times; should return first index
def test1_a : Array Int := #[5, 1, 5, 5]
def test1_key : Int := 5
def test1_Expected : Int := 0

-- Test case 2: key present in the middle
def test2_a : Array Int := #[10, 20, 30, 40]
def test2_key : Int := 30
def test2_Expected : Int := 2

-- Test case 3: key present at the last index
def test3_a : Array Int := #[7, 8, 9]
def test3_key : Int := 9
def test3_Expected : Int := 2

-- Test case 4: key absent in a non-empty array
def test4_a : Array Int := #[1, 2, 3, 4]
def test4_key : Int := 5
def test4_Expected : Int := (-1)

-- Test case 5: empty array (degenerate input)
def test5_a : Array Int := #[]
def test5_key : Int := 0
def test5_Expected : Int := (-1)

-- Test case 6: singleton array where key is present
def test6_a : Array Int := #[42]
def test6_key : Int := 42
def test6_Expected : Int := 0

-- Test case 7: singleton array where key is absent
def test7_a : Array Int := #[42]
def test7_key : Int := (-42)
def test7_Expected : Int := (-1)

-- Test case 8: array containing negative numbers; key is negative and present
def test8_a : Array Int := #[-3, -2, -1, 0, 1]
def test8_key : Int := (-1)
def test8_Expected : Int := 2

-- Test case 9: key = 0 present; first occurrence not at index 0
def test9_a : Array Int := #[1, 0, 0, 2]
def test9_key : Int := 0
def test9_Expected : Int := 1
end TestCases
