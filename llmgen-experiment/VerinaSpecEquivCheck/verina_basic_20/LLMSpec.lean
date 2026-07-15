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
    DistinctProduct: compute the product of all distinct integers appearing in an array.

    Natural language breakdown:
    1. Input is an array of integers `arr`.
    2. Only the set of distinct values appearing in `arr` matters; duplicates are ignored.
    3. The output is the product (integer multiplication) of all distinct values in `arr`.
    4. If `arr` is empty, the product over an empty collection is `1`.
    5. The order of multiplication does not matter.
-/

section Specs
-- Convert an array to a finset of the distinct values it contains.
-- This is a specification-level abstraction of “consider each unique integer only once”.
-- We avoid using `Array.toList` in specs.
def arrToFinset (arr : Array Int) : Finset Int :=
  arr.foldl (fun (s : Finset Int) (x : Int) => insert x s) (∅)

-- No input restrictions.
def precondition (arr : Array Int) : Prop :=
  True

-- The result equals the product of all distinct elements of the array.
-- `Finset.prod` uses `1` as the identity, hence the empty-array case yields `1`.
def postcondition (arr : Array Int) (result : Int) : Prop :=
  result = (arrToFinset arr).prod (fun (x : Int) => x)
end Specs

section Impl
method DistinctProduct (arr : Array Int)
  return (result : Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure 1

end Impl

section TestCases
-- Test case 1: empty array → product is 1
def test1_arr : Array Int := #[]
def test1_Expected : Int := 1

-- Test case 2: singleton
def test2_arr : Array Int := #[5]
def test2_Expected : Int := 5

-- Test case 3: all duplicates
def test3_arr : Array Int := #[2, 2, 2]
def test3_Expected : Int := 2

-- Test case 4: all unique positives
def test4_arr : Array Int := #[1, 2, 3]
def test4_Expected : Int := 6

-- Test case 5: mixed duplicates (distinct set {1,2,3})
def test5_arr : Array Int := #[1, 2, 2, 3, 1]
def test5_Expected : Int := 6

-- Test case 6: includes 0 (distinct set {0,5})
def test6_arr : Array Int := #[0, 5, 0]
def test6_Expected : Int := 0

-- Test case 7: includes negatives (distinct set {-1,2,3})
def test7_arr : Array Int := #[-1, 2, -1, 3]
def test7_Expected : Int := -6

-- Test case 8: negatives with duplicates (distinct set {-2,-3,4})
def test8_arr : Array Int := #[-2, -3, -2, 4, -3]
def test8_Expected : Int := 24

-- Test case 9: boundary-style mix containing -1, 0, 1
def test9_arr : Array Int := #[1, -1, 0]
def test9_Expected : Int := 0
end TestCases
