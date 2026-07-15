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
    MaxStrengthSubsetProduct: maximize the product of scores over all non-empty subsets.
    Natural language breakdown:
    1. The input is a non-empty list of integers `nums` representing student scores.
    2. A chosen group corresponds to selecting any non-empty subset of positions in the list.
    3. We model such a selection as a non-empty sublist `s` of `nums` (order-preserving pick of elements).
    4. The strength of a chosen group is the product of the integers in the chosen sublist.
    5. The required output is the maximum achievable strength among all non-empty selections.
    6. The output must be achievable by at least one valid non-empty selection.
    7. The output must be greater than or equal to the strength of every other valid non-empty selection.
-/

section Specs
-- Helper: product of a list of integers.
-- We use `foldl` to avoid relying on any additional list algebra imports.
-- Convention: the product of an empty list is 1, but empty selections are forbidden by `IsValidSelection`.
def listProd (xs : List Int) : Int :=
  xs.foldl (fun (acc : Int) (x : Int) => acc * x) 1

-- A valid selection is a non-empty sublist (order-preserving) of the original list.
def IsValidSelection (nums : List Int) (s : List Int) : Prop :=
  List.Sublist s nums ∧ s ≠ []

def precondition (nums : List Int) : Prop :=
  nums ≠ []

def postcondition (nums : List Int) (result : Int) : Prop :=
  -- Achievability: the result equals the product of some non-empty valid selection.
  (∃ s : List Int,
      IsValidSelection nums s ∧
      listProd s = result) ∧
  -- Maximality: every non-empty valid selection has product at most `result`.
  (∀ s : List Int,
      IsValidSelection nums s →
      listProd s ≤ result)
end Specs

section Impl
method MaxStrengthSubsetProduct (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical mix of positive and negative
-- Candidates: [3] -> 3, [-1] -> -1, [2] -> 2, [3,2] -> 6, [3,-1]->-3, [-1,2]->-2, [3,-1,2]->-6
-- Maximum is 6

def test1_nums : List Int := [3, -1, 2]
def test1_Expected : Int := 6

-- Test case 2: includes -1, 0, 1 (edge values)
-- Best is [1] -> 1

def test2_nums : List Int := [-1, 0, 1]
def test2_Expected : Int := 1

-- Test case 3: all zeros

def test3_nums : List Int := [0, 0]
def test3_Expected : Int := 0

-- Test case 4: singleton negative (only one nonempty subset)

def test4_nums : List Int := [-5]
def test4_Expected : Int := -5

-- Test case 5: all positive (best is product of all)

def test5_nums : List Int := [2, 3, 4]
def test5_Expected : Int := 24

-- Test case 6: two negatives allow a larger positive product when combined with positives
-- Best is [-2, -1, 3, 4] -> 24

def test6_nums : List Int := [-1, -2, 3, 4]
def test6_Expected : Int := 24

-- Test case 7: three negatives (best is product of the best pair)

def test7_nums : List Int := [-1, -2, -3]
def test7_Expected : Int := 6

-- Test case 8: singleton positive one

def test8_nums : List Int := [1]
def test8_Expected : Int := 1

-- Test case 9: zero with two negatives (best is their product)

def test9_nums : List Int := [0, -1, -2]
def test9_Expected : Int := 2

-- Recommend to validate: SMT handling of List.Sublist, integer multiplication semantics, maximality quantifier
end TestCases
