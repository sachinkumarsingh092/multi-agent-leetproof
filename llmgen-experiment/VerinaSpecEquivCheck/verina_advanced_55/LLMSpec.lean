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
    MostFrequentFirst: return the integer that appears most frequently in a non-empty list, breaking ties by first occurrence.
    Natural language breakdown:
    1. The input is a list of integers `xs` and it is guaranteed to be non-empty.
    2. For any integer `x`, its frequency in `xs` is the number of indices in `xs` whose element equals `x`.
    3. The output `result` must be an element of the input list.
    4. The frequency of `result` is maximal among all elements that occur in `xs`.
    5. If multiple elements have the same maximal frequency, the output must be the one whose first occurrence index in `xs` is minimal.
-/

section Specs
-- Helper: first index of `x` in `xs` if present; otherwise `xs.length`.
-- In the postcondition we only compare first indices for values known to be in `xs`.
def firstIndex (xs : List Int) (x : Int) : Nat :=
  (xs.findIdx? (fun y => y = x)).getD xs.length

-- Precondition: input list is non-empty.
def precondition (xs : List Int) : Prop :=
  xs ≠ []

-- Postcondition: `result` is a most frequent element, and among ties it occurs first.
def postcondition (xs : List Int) (result : Int) : Prop :=
  result ∈ xs ∧
  (∀ (y : Int), y ∈ xs → xs.count y ≤ xs.count result) ∧
  (∀ (y : Int), y ∈ xs → xs.count y = xs.count result → firstIndex xs result ≤ firstIndex xs y)
end Specs

section Impl
method MostFrequentFirst (xs : List Int)
  return (result : Int)
  require precondition xs
  ensures postcondition xs result
  do
  -- Placeholder implementation only.
  pure xs.head!

end Impl

section TestCases
-- Test case 1: typical case with a unique most frequent element.
def test1_xs : List Int := [1, 2, 2, 3]
def test1_Expected : Int := 2

-- Test case 2: singleton list.
def test2_xs : List Int := [42]
def test2_Expected : Int := 42

-- Test case 3: all elements equal.
def test3_xs : List Int := [7, 7, 7, 7]
def test3_Expected : Int := 7

-- Test case 4: tie on frequency, choose the one appearing first.
def test4_xs : List Int := [5, 6, 5, 6]
def test4_Expected : Int := 5

-- Test case 5: tie among three values, first occurrence decides.
def test5_xs : List Int := [3, 1, 2, 1, 2, 3]
def test5_Expected : Int := 3

-- Test case 6: includes negative numbers; unique most frequent is negative.
def test6_xs : List Int := [-1, -1, 0, 1]
def test6_Expected : Int := -1

-- Test case 7: all distinct values (frequency 1); must return the first element.
def test7_xs : List Int := [9, 8, 7, 6]
def test7_Expected : Int := 9

-- Test case 8: later element has higher frequency; ensure not always head.
def test8_xs : List Int := [10, 20, 10, 30, 20, 20]
def test8_Expected : Int := 20

-- Test case 9: tie in max frequency but first element is not the smallest numerically.
def test9_xs : List Int := [100, 1, 1, 100]
def test9_Expected : Int := 100
end TestCases
