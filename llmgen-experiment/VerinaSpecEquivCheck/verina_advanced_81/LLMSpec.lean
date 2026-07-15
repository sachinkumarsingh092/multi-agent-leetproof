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
    UniqueSortAsc: Remove all duplicates from a list of integers and return the unique elements in ascending order.
    Natural language breakdown:
    1. The input is a list of integers `arr`.
    2. The output is a list of integers `result`.
    3. Every element that appears in `result` must also appear in `arr`.
    4. Every element that appears in `arr` must appear in `result` (i.e., `result` contains exactly the set of elements from `arr`).
    5. The list `result` must contain no duplicate elements.
    6. The list `result` must be sorted in ascending order with respect to `Int`'s `≤`.
-/

section Specs
-- We use Mathlib's standard list predicates:
-- * `List.Nodup` for duplicate-freeness
-- * `List.Sorted (· ≤ ·)` for ascending order
-- * `x ∈ l` for membership

-- No preconditions are required.
def precondition (arr : List Int) : Prop :=
  True

def postcondition (arr : List Int) (result : List Int) : Prop :=
  result.Nodup ∧
  List.Sorted (· ≤ ·) result ∧
  (∀ x : Int, x ∈ result ↔ x ∈ arr)
end Specs

section Impl
method UniqueSortAsc (arr : List Int)
  return (result : List Int)
  require precondition arr
  ensures postcondition arr result
  do
  -- Placeholder implementation only.
  pure ([] : List Int)

end Impl

section TestCases
-- Test case 1: example-style mixed list with duplicates
def test1_arr : List Int := [3, 1, 2, 3, 2]
def test1_Expected : List Int := [1, 2, 3]

-- Test case 2: empty input
def test2_arr : List Int := []
def test2_Expected : List Int := []

-- Test case 3: singleton input
def test3_arr : List Int := [5]
def test3_Expected : List Int := [5]

-- Test case 4: all elements equal
def test4_arr : List Int := [7, 7, 7, 7]
def test4_Expected : List Int := [7]

-- Test case 5: already sorted with no duplicates
def test5_arr : List Int := [-3, -1, 0, 2, 9]
def test5_Expected : List Int := [-3, -1, 0, 2, 9]

-- Test case 6: reverse order with duplicates
def test6_arr : List Int := [5, 4, 4, 3, 2, 1, 1]
def test6_Expected : List Int := [1, 2, 3, 4, 5]

-- Test case 7: includes negative numbers and duplicates
def test7_arr : List Int := [-1, -2, 0, -2, 3, -1]
def test7_Expected : List Int := [-2, -1, 0, 3]

-- Test case 8: boundary-ish small values and duplicates
def test8_arr : List Int := [0, 1, 0, 1, 2]
def test8_Expected : List Int := [0, 1, 2]

-- Test case 9: mixture with large magnitude integers
def test9_arr : List Int := [1000000, -1000000, 0, 1000000, -5]
def test9_Expected : List Int := [-1000000, -5, 0, 1000000]
end TestCases
