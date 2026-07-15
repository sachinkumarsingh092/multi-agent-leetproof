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
    Longest Increasing Subsequence (LIS): compute the length of the longest strictly increasing subsequence.

    Natural language breakdown:
    1. Input is a list of integers `nums`.
    2. A subsequence is obtained by deleting zero or more elements without changing the order of remaining elements.
    3. A strictly increasing list means that every earlier element is strictly less than every later element.
    4. A strictly increasing subsequence of `nums` is any list `sub` such that `sub` is a sublist of `nums`.
    5. The desired result is the maximum possible length among all strictly increasing subsequences of `nums`.
    6. The empty list is a valid subsequence of any list and is strictly increasing.
    7. Therefore, if `nums` is empty, the result must be 0.
-/

section Specs
-- A list is strictly increasing if it is pairwise related by `<`.
-- This implies each element is < every later element, and in particular adjacent elements increase.
-- It also holds for [] and singletons.
def StrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (fun (a : Int) (b : Int) => a < b)

-- `List.Sublist sub nums` is the standard Mathlib relation for an order-preserving subsequence.
def IsIncSubseq (sub : List Int) (nums : List Int) : Prop :=
  List.Sublist sub nums ∧ StrictlyIncreasing sub

-- No input restrictions.
def precondition (nums : List Int) : Prop :=
  True

-- The result is the length of a longest strictly increasing subsequence:
-- (1) there exists an increasing subsequence with length exactly `result`
-- (2) every increasing subsequence has length at most `result`
def postcondition (nums : List Int) (result : Nat) : Prop :=
  (∃ sub : List Int, IsIncSubseq sub nums ∧ sub.length = result) ∧
  (∀ sub : List Int, IsIncSubseq sub nums → sub.length ≤ result)
end Specs

section Impl
method LongestIncreasingSubsequenceLength (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

prove_correct LongestIncreasingSubsequenceLength by sorry
end Impl

section TestCases
-- Test case 1: classic mixed sequence
-- LIS length is 4 (e.g., [2, 3, 7, 101])
def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Nat := 4

-- Test case 2: empty list
-- No elements, LIS length is 0
def test2_nums : List Int := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list
-- LIS length is 1
def test3_nums : List Int := [5]
def test3_Expected : Nat := 1

-- Test case 4: strictly decreasing list
-- Any singleton is increasing; maximum length is 1
def test4_nums : List Int := [5, 4, 3, 2, 1]
def test4_Expected : Nat := 1

-- Test case 5: strictly increasing list
-- Entire list is the LIS
def test5_nums : List Int := [1, 2, 3, 4]
def test5_Expected : Nat := 4

-- Test case 6: all duplicates
-- Strictly increasing forbids equality; maximum is 1
def test6_nums : List Int := [2, 2, 2]
def test6_Expected : Nat := 1

-- Test case 7: includes negatives and repeated values
-- One LIS is [-1, 3, 4, 5]
def test7_nums : List Int := [-1, 3, 4, 5, 2, 2, 2, 2]
def test7_Expected : Nat := 4

-- Test case 8: alternating with repeats (classic example)
-- One LIS is [0, 1, 2, 3]
def test8_nums : List Int := [0, 1, 0, 3, 2, 3]
def test8_Expected : Nat := 4

-- Test case 9: short list where LIS is not contiguous
-- One LIS is [1, 2]
def test9_nums : List Int := [3, 1, 2]
def test9_Expected : Nat := 2

-- Recommend to validate: test1_nums, test2_nums, test8_nums
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Nat) :
  result ≠ test8_Expected →
  ¬ postcondition test8_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
