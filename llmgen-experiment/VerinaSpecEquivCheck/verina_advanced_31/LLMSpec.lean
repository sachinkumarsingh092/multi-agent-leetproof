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
    LongestIncreasingSubsequenceLength: length of the longest strictly increasing subsequence

    Natural language breakdown:
    1. Input is a list of integers `xs : List Int`.
    2. A subsequence of `xs` is obtained by deleting zero or more elements without changing the
       order of the remaining elements.
    3. We formalize the subsequence relation using `List.Sublist ys xs`.
    4. A list `ys` is strictly increasing if every earlier element is strictly smaller than every
       later element; we formalize this as `ys.Pairwise (fun a b => a < b)`.
    5. The output `result : Nat` is the maximum possible length among all strictly increasing
       subsequences of `xs`.
    6. The empty list is a valid input; then the longest strictly increasing subsequence has
       length `0`.
-/

section Specs
-- Helper predicate: `ys` is a strictly increasing subsequence of `xs`.
-- `List.Sublist` captures the subsequence notion (delete elements, preserve order).
-- `Pairwise (fun a b => a < b)` captures strict increase across all earlier/later pairs.
def isStrictIncSubseq (xs : List Int) (ys : List Int) : Prop :=
  List.Sublist ys xs ∧ ys.Pairwise (fun a b => a < b)

-- No preconditions: LIS length is defined for all lists.
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition: `result` is the length of a longest strictly increasing subsequence.
-- 1) Upper bound: every strictly increasing subsequence has length ≤ result.
-- 2) Achievability: there exists a strictly increasing subsequence whose length is exactly result.
def postcondition (xs : List Int) (result : Nat) : Prop :=
  (∀ (ys : List Int), isStrictIncSubseq xs ys → ys.length ≤ result) ∧
  (∃ (ys : List Int), isStrictIncSubseq xs ys ∧ ys.length = result)
end Specs

section Impl
method LongestIncreasingSubsequenceLength (xs : List Int)
  return (result : Nat)
  require precondition xs
  ensures postcondition xs result
  do
    pure 0

end Impl

section TestCases
-- Test case 1: classic example
-- One LIS is [2,3,7,101], so length = 4

def test1_xs : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Nat := 4

-- Test case 2: empty list

def test2_xs : List Int := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list

def test3_xs : List Int := [42]
def test3_Expected : Nat := 1

-- Test case 4: already strictly increasing

def test4_xs : List Int := [1, 2, 3, 4, 5]
def test4_Expected : Nat := 5

-- Test case 5: strictly decreasing

def test5_xs : List Int := [5, 4, 3, 2, 1]
def test5_Expected : Nat := 1

-- Test case 6: all equal elements (strict increase disallows equality)

def test6_xs : List Int := [7, 7, 7, 7]
def test6_Expected : Nat := 1

-- Test case 7: duplicates with possible increases
-- One LIS is [1,2,3], so length = 3

def test7_xs : List Int := [1, 2, 2, 2, 3]
def test7_Expected : Nat := 3

-- Test case 8: includes negative numbers
-- One LIS is [-3,-2,-1], so length = 3

def test8_xs : List Int := [-1, -3, -2, -1]
def test8_Expected : Nat := 3

-- Test case 9: mixture with a longer subsequence later
-- One LIS is [0,2,6,9,11,15], so length = 6

def test9_xs : List Int := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
def test9_Expected : Nat := 6

-- Recommend to validate: test1_xs, test2_xs, test9_xs
end TestCases
