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
    LongestIncreasingSubsequenceLength: determine the length of the longest strictly increasing subsequence in a list of integers.
    Natural language breakdown:
    1. The input is a sequence of integers `nums`.
    2. A subsequence is obtained by deleting zero or more elements of `nums` without changing the relative order of remaining elements.
    3. A subsequence is strictly increasing if every earlier element is strictly less than every later element.
    4. Among all strictly increasing subsequences of `nums`, we consider their lengths.
    5. The output is the maximum such length.
    6. The empty subsequence is always allowed and has length 0, so the result is always defined and is nonnegative.
    7. The specification characterizes the result by (a) existence of an increasing subsequence achieving that length and
       (b) maximality: no other increasing subsequence is longer.
-/

section Specs
-- A list is strictly increasing when all earlier elements are < all later elements.
-- For linear orders like Int, `Pairwise (· < ·)` captures this notion.
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (fun a b => a < b)

-- A candidate list `s` is a valid strictly increasing subsequence of `nums`.
def isIncSubseq (nums : List Int) (s : List Int) : Prop :=
  s.Sublist nums ∧ isStrictlyIncreasing s

-- No preconditions: the result is defined for every input list.
def precondition (nums : List Int) : Prop :=
  True

-- The result is exactly the maximum length of a strictly increasing subsequence.
-- We phrase lengths as `Int.ofNat s.length` to match the required return type `Int`.
def postcondition (nums : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ s : List Int, isIncSubseq nums s ∧ Int.ofNat s.length = result) ∧
  (∀ t : List Int, isIncSubseq nums t → Int.ofNat t.length ≤ result)
end Specs

section Impl
method LongestIncreasingSubsequenceLength (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

prove_correct LongestIncreasingSubsequenceLength by sorry
end Impl

section TestCases
-- Test case 1: empty input
def test1_nums : List Int := []
def test1_Expected : Int := 0

-- Test case 2: singleton list
def test2_nums : List Int := [42]
def test2_Expected : Int := 1

-- Test case 3: strictly increasing list
def test3_nums : List Int := [1, 2, 3, 4, 5]
def test3_Expected : Int := 5

-- Test case 4: strictly decreasing list
def test4_nums : List Int := [5, 4, 3, 2, 1]
def test4_Expected : Int := 1

-- Test case 5: list with duplicates only (strictly increasing disallows equal steps)
def test5_nums : List Int := [2, 2, 2]
def test5_Expected : Int := 1

-- Test case 6: mixed list (classic LIS example)
def test6_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test6_Expected : Int := 4

-- Test case 7: includes negative numbers
def test7_nums : List Int := [-3, -2, -5, -1]
def test7_Expected : Int := 3

-- Test case 8: increasing subsequence must respect order (non-contiguous)
def test8_nums : List Int := [3, 1, 2]
def test8_Expected : Int := 2

-- Test case 9: repeated values with an increasing tail
def test9_nums : List Int := [0, 0, 0, 1, 2]
def test9_Expected : Int := 3
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
