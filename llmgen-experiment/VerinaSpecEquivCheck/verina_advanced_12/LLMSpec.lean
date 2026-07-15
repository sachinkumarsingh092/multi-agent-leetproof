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
    FirstDuplicate: return the first duplicated integer encountered when scanning a list from left to right.
    Natural language breakdown:
    1. Input is a list of integers.
    2. We conceptually scan the list from left to right.
    3. An index j is a "duplicate occurrence" if there exists an earlier index i < j with the same value.
    4. The function returns the value at the smallest index j that is a duplicate occurrence.
    5. If no index is a duplicate occurrence, the function returns none.
    6. The output type is Option Int: some x for the first duplicated value, none otherwise.
-/

section Specs
-- Helper: j is a duplicate occurrence if the element at j appears earlier.
-- We include j < lst.length so that all indexing operations are safe.
def DupAt (lst : List Int) (j : Nat) : Prop :=
  j < lst.length ∧ ∃ i : Nat, i < j ∧ lst[i]! = lst[j]!

-- Helper: j is the first index (smallest) that is a duplicate occurrence.
def IsFirstDupIndex (lst : List Int) (j : Nat) : Prop :=
  DupAt lst j ∧ ∀ k : Nat, k < j → ¬ DupAt lst k

-- No input restrictions.
def precondition (lst : List Int) : Prop :=
  True

def postcondition (lst : List Int) (result : Option Int) : Prop :=
  match result with
  | none =>
      -- No position is a duplicate occurrence.
      ∀ j : Nat, j < lst.length → ¬ DupAt lst j
  | some x =>
      -- There is a first duplicate index j, and x is the value at that position.
      ∃ j : Nat, IsFirstDupIndex lst j ∧ lst[j]! = x
end Specs

section Impl
method FirstDuplicate (lst : List Int)
  return (result : Option Int)
  require precondition lst
  ensures postcondition lst result
  do
  -- Placeholder implementation only.
  pure none

end Impl

section TestCases
-- Test case 1: typical with a clear first duplicate (value 2 at index 2)
def test1_lst : List Int := [1, 2, 2, 3]
def test1_Expected : Option Int := some 2

-- Test case 2: empty list
def test2_lst : List Int := []
def test2_Expected : Option Int := none

-- Test case 3: singleton list
def test3_lst : List Int := [42]
def test3_Expected : Option Int := none

-- Test case 4: no duplicates
def test4_lst : List Int := [1, 2, 3, 4, 5]
def test4_Expected : Option Int := none

-- Test case 5: duplicate appears immediately (first duplicate value 0)
def test5_lst : List Int := [0, 0, 1]
def test5_Expected : Option Int := some 0

-- Test case 6: multiple duplicates; earliest second occurrence determines answer
-- 2 duplicates at j=2, 1 duplicates later, so answer is 2.
def test6_lst : List Int := [2, 1, 2, 1]
def test6_Expected : Option Int := some 2

-- Test case 7: earliest second occurrence is a later value, not the first value in the list
-- 1 duplicates at index 2; 0 duplicates at index 3, so answer is 1.
def test7_lst : List Int := [0, 1, 1, 0]
def test7_Expected : Option Int := some 1

-- Test case 8: negative integers and duplicates (first duplicate -1)
def test8_lst : List Int := [-1, 2, -1, 2]
def test8_Expected : Option Int := some (-1)

-- Test case 9: all elements the same
def test9_lst : List Int := [7, 7, 7, 7]
def test9_Expected : Option Int := some 7

-- Recommend to validate: test1_lst, test6_lst, test8_lst
end TestCases
