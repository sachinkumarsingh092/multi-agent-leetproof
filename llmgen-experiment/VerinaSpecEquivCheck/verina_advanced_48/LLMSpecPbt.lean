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
    MergeSortInt: Sort a list of integers in ascending order.
    Natural language breakdown:
    1. Input is a list of integers.
    2. Output is a list of integers.
    3. Output must be sorted in nondecreasing (ascending) order with respect to the usual integer order (≤).
    4. Output must contain exactly the same elements as the input, including duplicates (multiplicities are preserved).
    5. For empty lists and singleton lists, the output is trivially sorted and must contain exactly those elements.
    6. The specification is algorithm-agnostic: it does not prescribe merge sort steps, only the required result properties.
-/

section Specs
-- Preconditions: merge sort is defined for all lists of integers.
-- Note: SpecDSL requires the parameter binders of `precondition` and `postcondition`
-- to match exactly (same names/types/order).
def precondition (list : List Int) : Prop :=
  True

-- Postconditions:
-- 1) The result is sorted (ascending).
-- 2) The result contains exactly the same elements with the same multiplicities as the input,
--    expressed as equality of their coerced multisets.
def postcondition (list : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ ((result : Multiset Int) = (list : Multiset Int))
end Specs

section Impl
method MergeSortInt (list : List Int)
  return (result : List Int)
  require precondition list
  ensures postcondition list result
  do
  pure ([] : List Int)  -- placeholder body only

prove_correct MergeSortInt by sorry
end Impl

section TestCases
-- Test case 1: typical unsorted list
-- input: [3, 1, 2]
-- expected: [1, 2, 3]
def test1_list : List Int := [3, 1, 2]
def test1_Expected : List Int := [1, 2, 3]

-- Test case 2: empty list (degenerate)
def test2_list : List Int := ([] : List Int)
def test2_Expected : List Int := ([] : List Int)

-- Test case 3: singleton list (degenerate)
def test3_list : List Int := [5]
def test3_Expected : List Int := [5]

-- Test case 4: already sorted with negatives/positives
def test4_list : List Int := [-3, -1, 0, 2, 10]
def test4_Expected : List Int := [-3, -1, 0, 2, 10]

-- Test case 5: reverse sorted list (includes 0)
def test5_list : List Int := [4, 3, 2, 1, 0]
def test5_Expected : List Int := [0, 1, 2, 3, 4]

-- Test case 6: list with duplicates
def test6_list : List Int := [2, 1, 2, 1, 2]
def test6_Expected : List Int := [1, 1, 2, 2, 2]

-- Test case 7: negatives and positives intermixed
def test7_list : List Int := [0, -1, 3, -2, 2]
def test7_Expected : List Int := [-2, -1, 0, 2, 3]

-- Test case 8: all elements equal
def test8_list : List Int := [7, 7, 7, 7]
def test8_Expected : List Int := [7, 7, 7, 7]

-- Test case 9: large magnitude values
def test9_list : List Int := [1000000, -1000000, 5, -5, 0]
def test9_Expected : List Int := [-1000000, -5, 0, 5, 1000000]

-- Recommend to validate: test1_list, test6_list, test9_list
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : List Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_list result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
