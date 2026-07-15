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
    MaxElementOfNatList: return the maximum element of a non-empty list of natural numbers.

    Natural language breakdown:
    1. The input is a list of natural numbers.
    2. The input list is required to be non-empty.
    3. The output is a natural number.
    4. The output value must be an element of the input list.
    5. The output value must be greater than or equal to every element of the input list.
    6. Because the output is an element and an upper bound, it is the (value of the) maximum element of the list.
-/

section Specs
-- A value is a maximum element of a list when it is contained in the list
-- and it is an upper bound for all elements of the list.

def precondition (lst : List Nat) : Prop :=
  lst ≠ []

def postcondition (lst : List Nat) (result : Nat) : Prop :=
  result ∈ lst ∧
  (∀ (x : Nat), x ∈ lst → x ≤ result)
end Specs

section Impl
method MaxElementOfNatList (lst : List Nat)
  return (result : Nat)
  require precondition lst
  ensures postcondition lst result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical multi-element list
def test1_lst : List Nat := [1, 4, 2, 10, 6]
def test1_Expected : Nat := 10

-- Test case 2: singleton list with 0
def test2_lst : List Nat := [0]
def test2_Expected : Nat := 0

-- Test case 3: singleton list with 1
def test3_lst : List Nat := [1]
def test3_Expected : Nat := 1

-- Test case 4: list with repeated maximum
def test4_lst : List Nat := [3, 7, 7, 2]
def test4_Expected : Nat := 7

-- Test case 5: strictly decreasing list
def test5_lst : List Nat := [9, 8, 7, 6]
def test5_Expected : Nat := 9

-- Test case 6: list with many zeros
def test6_lst : List Nat := [0, 0, 0, 2, 0]
def test6_Expected : Nat := 2

-- Test case 7: maximum at the end
def test7_lst : List Nat := [2, 3, 4, 5]
def test7_Expected : Nat := 5

-- Test case 8: larger values
def test8_lst : List Nat := [1000, 42, 999, 1001, 0]
def test8_Expected : Nat := 1001

-- Test case 9: maximum appears multiple times and list contains 0 and 1
def test9_lst : List Nat := [0, 1, 5, 1, 5, 2]
def test9_Expected : Nat := 5
end TestCases
