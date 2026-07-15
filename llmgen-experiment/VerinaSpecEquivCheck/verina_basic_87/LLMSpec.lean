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
    ArraySortNondecreasing: Sort an array of integers into non-decreasing order while preserving the multiset of elements.

    Natural language breakdown:
    1. The input is an array `a : Array Int`.
    2. The output is an array `result : Array Int`.
    3. The output array must have the same size as the input array.
    4. The output must be sorted in non-decreasing order: for any indices i < j within bounds, result[i] ≤ result[j].
    5. The output must contain exactly the same elements as the input, counting multiplicities.
    6. There are no required input constraints; all arrays are valid inputs.
-/

section Specs
-- Helper: non-decreasing sortedness for arrays using Nat indices.
-- Strong form: for all i < j within bounds, arr[i] ≤ arr[j].
def ArrayNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: count how many times a value occurs in an array.
-- This is a purely observational property used to express multiset equality.
def elemCount (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if decide (x = v) then acc + 1 else acc) 0

-- Helper: two arrays contain exactly the same multiset of elements (same size and same counts).
def SameMultiset (x : Array Int) (y : Array Int) : Prop :=
  x.size = y.size ∧
  ∀ (v : Int), elemCount x v = elemCount y v

-- No preconditions: any array is a valid input to sorting.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ArrayNondecreasing result ∧
  SameMultiset result a
end Specs

section Impl
method ArraySortNondecreasing (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
    -- Placeholder implementation only.
    pure a

end Impl

section TestCases
-- Test case 1: example-style mixed values
-- Input: [3, 1, 2] -> Expected: [1, 2, 3]
def test1_a : Array Int := #[3, 1, 2]
def test1_Expected : Array Int := #[1, 2, 3]

-- Test case 2: empty array (boundary)
def test2_a : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: singleton array (boundary)
def test3_a : Array Int := #[42]
def test3_Expected : Array Int := #[42]

-- Test case 4: already sorted array
def test4_a : Array Int := #[-3, -1, 0, 2, 10]
def test4_Expected : Array Int := #[-3, -1, 0, 2, 10]

-- Test case 5: reverse-sorted array
def test5_a : Array Int := #[5, 4, 3, 2, 1]
def test5_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 6: duplicates present
def test6_a : Array Int := #[2, 1, 2, 1, 0]
def test6_Expected : Array Int := #[0, 1, 1, 2, 2]

-- Test case 7: all elements equal
def test7_a : Array Int := #[7, 7, 7, 7]
def test7_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 8: mixture with negatives and duplicates
def test8_a : Array Int := #[-1, 3, -1, 2, 0]
def test8_Expected : Array Int := #[-1, -1, 0, 2, 3]

-- Test case 9: includes negative/zero/positive boundary values (-1, 0, 1)
def test9_a : Array Int := #[-1, 0, 1, 0, -1]
def test9_Expected : Array Int := #[-1, -1, 0, 0, 1]

-- Recommend to validate: sortedness, multiset preservation, boundary cases
end TestCases
