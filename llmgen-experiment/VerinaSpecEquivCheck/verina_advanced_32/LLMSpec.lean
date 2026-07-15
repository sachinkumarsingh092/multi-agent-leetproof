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
    LongestIncreasingSubsequenceLength: find the length of the longest strictly increasing subsequence of a list of integers.

    Natural language breakdown:
    1. The input is a list of integers `numbers`.
    2. A subsequence is obtained by deleting zero or more elements without changing the order of the remaining elements.
    3. A strictly increasing subsequence is one where every earlier element is strictly less than every later element.
    4. The output is a natural number `result` representing the maximum length among all strictly increasing subsequences of `numbers`.
    5. The empty list has longest increasing subsequence length 0.
    6. The specification characterizes `result` by:
       a. Existence: there exists a strictly increasing subsequence of `numbers` with length exactly `result`.
       b. Maximality: any strictly increasing subsequence of `numbers` has length at most `result`.
-/

section Specs
-- A list is strictly increasing when all pairs of positions are strictly ordered.
-- `Pairwise (· < ·)` implies in particular that adjacent elements are strictly increasing.
def isStrictlyIncreasing (xs : List Int) : Prop :=
  xs.Pairwise (fun a b => a < b)

-- A subsequence relation: `xs` is a subsequence of `numbers` if it can be obtained
-- by deleting elements from `numbers` without reordering.
-- In this library setup, `List.Sublist` is the available relation for this notion.
def isSubsequence (xs : List Int) (numbers : List Int) : Prop :=
  List.Sublist xs numbers

def precondition (numbers : List Int) : Prop :=
  True

def postcondition (numbers : List Int) (result : Nat) : Prop :=
  (∃ (s : List Int),
      isSubsequence s numbers ∧
      isStrictlyIncreasing s ∧
      s.length = result) ∧
  (∀ (t : List Int),
      isSubsequence t numbers →
      isStrictlyIncreasing t →
      t.length ≤ result)
end Specs

section Impl
method LongestIncreasingSubsequenceLength (numbers : List Int)
  return (result : Nat)
  require precondition numbers
  ensures postcondition numbers result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: example mixed sequence
-- One LIS is [2, 3, 7, 18] (or [2, 3, 7, 101]) of length 4.
def test1_numbers : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Nat := 4

-- Test case 2: empty list
-- LIS length is 0.
def test2_numbers : List Int := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list
-- LIS length is 1.
def test3_numbers : List Int := [42]
def test3_Expected : Nat := 1

-- Test case 4: already strictly increasing
-- LIS length equals list length.
def test4_numbers : List Int := [-3, -2, -1, 0, 1, 2]
def test4_Expected : Nat := 6

-- Test case 5: strictly decreasing
-- Any strictly increasing subsequence can only have length 1.
def test5_numbers : List Int := [5, 4, 3, 2, 1]
def test5_Expected : Nat := 1

-- Test case 6: all duplicates
-- Strictly increasing forbids equal adjacent/elements, so length is 1 (or 0 for empty, but list is nonempty here).
def test6_numbers : List Int := [7, 7, 7, 7]
def test6_Expected : Nat := 1

-- Test case 7: duplicates with a possible increase
-- One LIS is [1, 2, 3] of length 3.
def test7_numbers : List Int := [1, 2, 2, 2, 3]
def test7_Expected : Nat := 3

-- Test case 8: includes negative and positive values
-- One LIS is [-1, 0, 2, 3] of length 4.
def test8_numbers : List Int := [-1, 3, 4, 0, 2, 2, 2, 3]
def test8_Expected : Nat := 4

-- Test case 9: alternating ups and downs
-- One LIS is [1, 2, 3, 4, 6] of length 5.
def test9_numbers : List Int := [1, 5, 2, 3, 4, 0, 6]
def test9_Expected : Nat := 5

-- Recommend to validate: empty list handling, duplicates under strictness, negative/positive mixes
end TestCases
