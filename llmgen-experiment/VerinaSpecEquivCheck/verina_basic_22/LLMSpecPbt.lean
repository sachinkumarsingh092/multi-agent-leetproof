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
    SymmetricDifferenceSortedDedup: Identify dissimilar elements between two arrays of integers.

    Natural language breakdown:
    1. Inputs are two arrays `a` and `b` of integers.
    2. An integer value is considered "dissimilar" if it appears in exactly one of the arrays.
    3. The output is an array containing all such dissimilar values.
    4. Duplicates in the inputs do not affect the output (membership is set-like).
    5. The output must contain no duplicates: each value appears at most once.
    6. The output must be sorted in nondecreasing (ascending) order.
    7. The output must contain no other values besides the dissimilar ones.
    8. If there are no dissimilar values, the output is the empty array.
-/

section Specs
-- Helper: array is sorted in nondecreasing order, using Nat indices and `arr[i]!`.
-- This avoids `Fin` index proof complexity.
def isSorted (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: no duplicates in an array, expressed via index inequality.
def arrayNodup (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < arr.size → j < arr.size → i ≠ j → arr[i]! ≠ arr[j]!

-- No preconditions: any integer arrays are allowed.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) Membership in `result` is exactly the symmetric difference of membership in `a` and `b`.
-- 2) `result` has no duplicates.
-- 3) `result` is sorted in nondecreasing order.
-- These properties together uniquely characterize the (canonical) output as the sorted deduplicated
-- list of all elements that appear in exactly one input.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  (∀ (x : Int), x ∈ result ↔ ((x ∈ a ∧ x ∉ b) ∨ (x ∈ b ∧ x ∉ a))) ∧
  arrayNodup result ∧
  isSorted result
end Specs

section Impl
method SymmetricDifferenceSortedDedup (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure (#[])

prove_correct SymmetricDifferenceSortedDedup by sorry
end Impl

section TestCases
-- Test case 1: typical overlap
-- a = [1,2,3], b = [3,4] => symmetric difference = [1,2,4]
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[3, 4]
def test1_Expected : Array Int := #[1, 2, 4]

-- Test case 2: both empty
-- => []
def test2_a : Array Int := #[]
def test2_b : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: left empty, right has duplicates
-- a = [], b = [1,1,2] => [1,2]
def test3_a : Array Int := #[]
def test3_b : Array Int := #[1, 1, 2]
def test3_Expected : Array Int := #[1, 2]

-- Test case 4: right empty, left has duplicates
-- a = [-1,0,0], b = [] => [-1,0]
def test4_a : Array Int := #[-1, 0, 0]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[-1, 0]

-- Test case 5: identical sets (even if multiplicities differ)
-- a = [5,5,6], b = [6,5] => []
def test5_a : Array Int := #[5, 5, 6]
def test5_b : Array Int := #[6, 5]
def test5_Expected : Array Int := #[]

-- Test case 6: disjoint arrays with duplicates
-- a = [2,2,1], b = [4,3,3] => [1,2,3,4]
def test6_a : Array Int := #[2, 2, 1]
def test6_b : Array Int := #[4, 3, 3]
def test6_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 7: negatives and overlap
-- a = [-2,-1,0], b = [-1,1] => [-2,0,1]
def test7_a : Array Int := #[-2, -1, 0]
def test7_b : Array Int := #[-1, 1]
def test7_Expected : Array Int := #[-2, 0, 1]

-- Test case 8: singleton arrays equal
-- a = [0], b = [0] => []
def test8_a : Array Int := #[0]
def test8_b : Array Int := #[0]
def test8_Expected : Array Int := #[]

-- Test case 9: singleton arrays different
-- a = [0], b = [1] => [0,1]
def test9_a : Array Int := #[0]
def test9_b : Array Int := #[1]
def test9_Expected : Array Int := #[0, 1]

-- Recommend to validate: membership symmetric-difference, sortedness, no-duplicates
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Array Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_a test3_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
