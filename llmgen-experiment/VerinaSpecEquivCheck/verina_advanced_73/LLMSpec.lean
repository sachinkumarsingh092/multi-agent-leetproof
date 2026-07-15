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
    FirstMissingNat: Find the smallest natural number that does not occur in an increasingly sorted list.

    Natural language breakdown:
    1. The input is a finite list of natural numbers.
    2. The list is sorted in strictly increasing order.
    3. The output is a natural number `result`.
    4. `result` is not an element of the input list.
    5. Every natural number strictly smaller than `result` is an element of the input list.
    6. Therefore, `result` is the smallest natural number missing from the list.
-/

section Specs
-- `result` is the minimal excluded natural number (mex) of `l`.
-- This property uniquely characterizes the intended output.
def isMex (l : List Nat) (result : Nat) : Prop :=
  result ∉ l ∧ (∀ (n : Nat), n < result → n ∈ l)

-- The task statement says the input list is sorted in increasing order.
def precondition (l : List Nat) : Prop :=
  l.Sorted (· < ·)

def postcondition (l : List Nat) (result : Nat) : Prop :=
  isMex l result
end Specs

section Impl
method FirstMissingNat (l : List Nat)
  return (result : Nat)
  require precondition l
  ensures postcondition l result
  do
    pure 0  -- placeholder

end Impl

section TestCases
-- Test case 1: empty list (edge case) => mex is 0
def test1_l : List Nat := []
def test1_Expected : Nat := 0

-- Test case 2: list starts at 1 (so 0 is missing)
def test2_l : List Nat := [1, 2, 3, 4]
def test2_Expected : Nat := 0

-- Test case 3: consecutive prefix from 0
def test3_l : List Nat := [0, 1, 2]
def test3_Expected : Nat := 3

-- Test case 4: missing 1
def test4_l : List Nat := [0, 2, 3, 4]
def test4_Expected : Nat := 1

-- Test case 5: singleton list containing 0
def test5_l : List Nat := [0]
def test5_Expected : Nat := 1

-- Test case 6: missing in the middle
def test6_l : List Nat := [0, 1, 3, 4]
def test6_Expected : Nat := 2

-- Test case 7: longer consecutive prefix
def test7_l : List Nat := [0, 1, 2, 3, 4, 5]
def test7_Expected : Nat := 6

-- Test case 8: missing 3
def test8_l : List Nat := [0, 1, 2, 4, 5, 6]
def test8_Expected : Nat := 3

-- Test case 9: larger values with a small gap at 2
def test9_l : List Nat := [0, 1, 3, 10, 11]
def test9_Expected : Nat := 2
end TestCases
