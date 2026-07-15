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
    InsertionSort: sort a list of integers in ascending (non-decreasing) order.

    Natural language breakdown:
    1. The input is a list of integers.
    2. The output is a list of integers.
    3. The output list must be sorted in non-decreasing order.
    4. The output list must contain exactly the same elements as the input list, counting multiplicity.
    5. Therefore the output is a permutation of the input.
-/

section Specs
-- We use Mathlib's predicates:
-- * `l.Sorted (· ≤ ·)` for non-decreasing sortedness.
-- * `List.Perm` to express that two lists are permutations (same multiset of elements).

def precondition (l : List Int) : Prop :=
  True

def postcondition (l : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ List.Perm result l
end Specs

section Impl
method InsertionSort (l : List Int)
  return (result : List Int)
  require precondition l
  ensures postcondition l result
  do
  -- Placeholder body only (not a real implementation)
  pure l

prove_correct InsertionSort by sorry
end Impl

section TestCases
-- Test case 1: example-like mixed list with duplicates
def test1_l : List Int := [3, 1, 2, 1]
def test1_Expected : List Int := [1, 1, 2, 3]

-- Test case 2: empty list
def test2_l : List Int := []
def test2_Expected : List Int := []

-- Test case 3: singleton list
def test3_l : List Int := [5]
def test3_Expected : List Int := [5]

-- Test case 4: already sorted list
def test4_l : List Int := [-3, -1, 0, 2, 2, 10]
def test4_Expected : List Int := [-3, -1, 0, 2, 2, 10]

-- Test case 5: reverse sorted list
def test5_l : List Int := [5, 4, 3, 2, 1, 0]
def test5_Expected : List Int := [0, 1, 2, 3, 4, 5]

-- Test case 6: all elements equal
def test6_l : List Int := [7, 7, 7, 7]
def test6_Expected : List Int := [7, 7, 7, 7]

-- Test case 7: contains negative and positive values with repeats
def test7_l : List Int := [-1, 3, -1, 2, 0]
def test7_Expected : List Int := [-1, -1, 0, 2, 3]

-- Test case 8: duplicates and zeros
def test8_l : List Int := [0, 2, 0, 1, 2, 1, 0]
def test8_Expected : List Int := [0, 0, 0, 1, 1, 2, 2]

-- Test case 9: larger mixed list
def test9_l : List Int := [10, -5, 3, 3, 8, -2, 0, 1]
def test9_Expected : List Int := [-5, -2, 0, 1, 3, 3, 8, 10]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : List Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_l result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
