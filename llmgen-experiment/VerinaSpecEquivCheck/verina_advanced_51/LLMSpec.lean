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
    MergeSortedIntLists: merge two sorted (non-decreasing) lists of integers into one sorted list.
    **Important: complexity should be O(a.length + b.length)**
    Natural language breakdown:
    1. Inputs are two lists a and b of integers.
    2. Each input list is sorted in non-decreasing order.
    3. The output is a list of integers.
    4. The output list is sorted in non-decreasing order.
    5. The output contains exactly all elements from a and b, counting duplicates.
    6. No elements other than those from a and b appear in the output.
    7. The output length equals a.length + b.length.
-/

section Specs
-- Helper: non-decreasing sortedness for Int lists.
-- Mathlib provides `List.Sorted`.
def sortedND (l : List Int) : Prop :=
  l.Sorted (fun x y => x ≤ y)

-- Precondition: both input lists are sorted in non-decreasing order.
def precondition (a : List Int) (b : List Int) : Prop :=
  sortedND a ∧ sortedND b

-- Postcondition:
-- 1) result is sorted in non-decreasing order
-- 2) result contains exactly all elements from a and b, counting duplicates
-- 3) result length equals sum of input lengths
-- Note: we avoid `List.toMultiset` (not available in this environment) and instead
-- specify multiplicities using `List.count`.
def postcondition (a : List Int) (b : List Int) (result : List Int) : Prop :=
  sortedND result ∧
  (∀ x : Int, result.count x = a.count x + b.count x) ∧
  result.length = a.length + b.length
end Specs

section Impl
method MergeSortedIntLists (a : List Int) (b : List Int)
  return (result : List Int)
  require precondition a b
  ensures postcondition a b result
  do
  -- Placeholder body only; real implementation should merge in O(a.length + b.length).
  pure ([] : List Int)

end Impl

section TestCases
-- Test case 1: typical merge with interleaving
-- (example from the prompt)
def test1_a : List Int := [1, 3, 5]
def test1_b : List Int := [2, 4, 6]
def test1_Expected : List Int := [1, 2, 3, 4, 5, 6]

-- Test case 2: one side empty (edge)
def test2_a : List Int := ([] : List Int)
def test2_b : List Int := [0, 1]
def test2_Expected : List Int := [0, 1]

-- Test case 3: both empty (degenerate)
def test3_a : List Int := ([] : List Int)
def test3_b : List Int := ([] : List Int)
def test3_Expected : List Int := ([] : List Int)

-- Test case 4: duplicates across both lists
def test4_a : List Int := [1, 2, 2, 5]
def test4_b : List Int := [2, 2, 3]
def test4_Expected : List Int := [1, 2, 2, 2, 2, 3, 5]

-- Test case 5: negatives and positives
def test5_a : List Int := [-5, -1, 0]
def test5_b : List Int := [-3, 2, 2]
def test5_Expected : List Int := [-5, -3, -1, 0, 2, 2]

-- Test case 6: all elements of a are less than all elements of b
def test6_a : List Int := [-2, -1]
def test6_b : List Int := [0, 0, 7]
def test6_Expected : List Int := [-2, -1, 0, 0, 7]

-- Test case 7: all elements of b are less than all elements of a
def test7_a : List Int := [10, 10]
def test7_b : List Int := [-1, 3, 9]
def test7_Expected : List Int := [-1, 3, 9, 10, 10]

-- Test case 8: singleton lists (edge)
def test8_a : List Int := [1]
def test8_b : List Int := [1]
def test8_Expected : List Int := [1, 1]

-- Test case 9: uneven lengths, repeated plateau values
def test9_a : List Int := [0, 0, 0, 1]
def test9_b : List Int := [0, 2]
def test9_Expected : List Int := [0, 0, 0, 0, 1, 2]

-- Recommend to validate: sortedness, multiplicity via count, length preservation
end TestCases
