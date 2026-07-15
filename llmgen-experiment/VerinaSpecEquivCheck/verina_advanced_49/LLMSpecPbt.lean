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
    MergeSortedLists: merge two ascendingly sorted lists of integers into a single ascendingly sorted list.
    Natural language breakdown:
    1. The inputs are two lists of integers, each already sorted in ascending order.
    2. The output is a list of integers that contains every element from both input lists.
    3. Element multiplicities are preserved: each integer appears in the output exactly as many times as it appears across both inputs.
    4. The output list is sorted in ascending order.
    5. The output length equals the sum of input lengths.
-/

section Specs
-- A simple, count-based multiset equality notion for lists of Int.
-- This avoids needing a separate reference implementation while precisely capturing
-- that the result contains exactly the elements from both inputs, with multiplicity.
def sameBag (a : List Int) (b : List Int) : Prop :=
  ∀ x : Int, a.count x = b.count x

-- Preconditions: both inputs are sorted ascending.
-- We use Mathlib's `List.Sorted` predicate.
def precondition (arr1 : List Int) (arr2 : List Int) : Prop :=
  arr1.Sorted (· ≤ ·) ∧ arr2.Sorted (· ≤ ·)

-- Postconditions:
-- 1) result is sorted ascending
-- 2) result has exactly the same multiset of elements as arr1 ++ arr2
-- 3) result length is the sum of the input lengths
-- Together these characterize the intended merge result.
def postcondition (arr1 : List Int) (arr2 : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧
  sameBag result (arr1 ++ arr2) ∧
  result.length = arr1.length + arr2.length
end Specs

section Impl
method MergeSortedLists (arr1 : List Int) (arr2 : List Int)
  return (result : List Int)
  require precondition arr1 arr2
  ensures postcondition arr1 arr2 result
  do
  pure []

prove_correct MergeSortedLists by sorry
end Impl

section TestCases
-- Test case 1: typical merge with interleaving
def test1_arr1 : List Int := [1, 3, 5]
def test1_arr2 : List Int := [2, 4, 6]
def test1_Expected : List Int := [1, 2, 3, 4, 5, 6]

-- Test case 2: first list empty
def test2_arr1 : List Int := []
def test2_arr2 : List Int := [0, 1, 2]
def test2_Expected : List Int := [0, 1, 2]

-- Test case 3: second list empty
def test3_arr1 : List Int := [-2, 0, 3]
def test3_arr2 : List Int := []
def test3_Expected : List Int := [-2, 0, 3]

-- Test case 4: both lists empty
def test4_arr1 : List Int := []
def test4_arr2 : List Int := []
def test4_Expected : List Int := []

-- Test case 5: duplicates across lists
def test5_arr1 : List Int := [1, 2, 2, 5]
def test5_arr2 : List Int := [2, 2, 3]
def test5_Expected : List Int := [1, 2, 2, 2, 2, 3, 5]

-- Test case 6: negative numbers and zeros
def test6_arr1 : List Int := [-5, -1, 0]
def test6_arr2 : List Int := [-3, -2, 4]
def test6_Expected : List Int := [-5, -3, -2, -1, 0, 4]

-- Test case 7: singleton lists
def test7_arr1 : List Int := [1]
def test7_arr2 : List Int := [1]
def test7_Expected : List Int := [1, 1]

-- Test case 8: one list entirely less than the other
def test8_arr1 : List Int := [0, 1, 2]
def test8_arr2 : List Int := [10, 11]
def test8_Expected : List Int := [0, 1, 2, 10, 11]

-- Test case 9: one list entirely greater than the other
def test9_arr1 : List Int := [10, 20]
def test9_arr2 : List Int := [-2, -1, 0]
def test9_Expected : List Int := [-2, -1, 0, 10, 20]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : List Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_arr1 test3_arr2 result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
