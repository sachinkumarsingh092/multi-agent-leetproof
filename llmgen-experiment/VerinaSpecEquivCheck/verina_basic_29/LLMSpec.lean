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
    RemoveAtIndex: remove the element of an integer array at a given valid index.
    Natural language breakdown:
    1. Input is an array s of integers and an index k (0-indexed) as a natural number.
    2. The index k is assumed to be valid: k < s.size.
    3. The output is an array result that contains all elements of s except the element at index k.
    4. All elements strictly before k keep the same index in result.
    5. All elements strictly after k are shifted left by one index in result.
    6. Therefore result.size is exactly s.size - 1.
-/

section Specs
-- No custom helpers are required.

def precondition (s : Array Int) (k : Nat) : Prop :=
  k < s.size

def postcondition (s : Array Int) (k : Nat) (result : Array Int) : Prop :=
  result.size = s.size - 1 ∧
  (∀ (i : Nat), i < result.size →
      ((i < k → result[i]! = s[i]!) ∧
       (k ≤ i → (i + 1 < s.size ∧ result[i]! = s[i + 1]!))))
end Specs

section Impl
method RemoveAtIndex (s : Array Int) (k : Nat)
  return (result : Array Int)
  require precondition s k
  ensures postcondition s k result
  do
  pure (#[] : Array Int)  -- placeholder body

end Impl

section TestCases
-- Test case 1: typical example; remove middle element
def test1_s : Array Int := #[10, 20, 30, 40]
def test1_k : Nat := 2
def test1_Expected : Array Int := #[10, 20, 40]

-- Test case 2: remove first element (k = 0)
def test2_s : Array Int := #[5, 6, 7]
def test2_k : Nat := 0
def test2_Expected : Array Int := #[6, 7]

-- Test case 3: remove last element (k = size - 1)
def test3_s : Array Int := #[5, 6, 7]
def test3_k : Nat := 2
def test3_Expected : Array Int := #[5, 6]

-- Test case 4: singleton array, removing the only element
def test4_s : Array Int := #[42]
def test4_k : Nat := 0
def test4_Expected : Array Int := (#[] : Array Int)

-- Test case 5: array with negative numbers, remove element at index 1
def test5_s : Array Int := #[-3, -2, -1, 0]
def test5_k : Nat := 1
def test5_Expected : Array Int := #[-3, -1, 0]

-- Test case 6: remove element from a length-2 array at index 0
def test6_s : Array Int := #[9, 8]
def test6_k : Nat := 0
def test6_Expected : Array Int := #[8]

-- Test case 7: remove element from a length-2 array at index 1
def test7_s : Array Int := #[9, 8]
def test7_k : Nat := 1
def test7_Expected : Array Int := #[9]

-- Test case 8: array with repeated values, remove one occurrence
def test8_s : Array Int := #[1, 1, 1, 1]
def test8_k : Nat := 2
def test8_Expected : Array Int := #[1, 1, 1]

-- Test case 9: larger array, remove near the end
def test9_s : Array Int := #[0, 1, 2, 3, 4, 5]
def test9_k : Nat := 4
def test9_Expected : Array Int := #[0, 1, 2, 3, 5]
end TestCases
