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
    LongestIncreasingSubsequenceLength: compute the length of the longest strictly increasing subsequence of an input list of integers.
    Natural language breakdown:
    1. The input is a list of integers `nums`.
    2. A subsequence is obtained by deleting zero or more elements without changing the order of the remaining elements.
    3. A subsequence is strictly increasing if every earlier element is strictly less than every later element.
    4. The output is a natural number `result`, interpreted as the maximum length among all strictly increasing subsequences of `nums`.
    5. If `nums` is empty, the only subsequence is empty, so the result is 0.
    6. If `nums` is nonempty, the result is at least 1.
    7. The result must be achievable by some strictly increasing subsequence, and it must be an upper bound on the lengths of all strictly increasing subsequences.
-/

section Specs
-- A list is strictly increasing when it is pairwise ordered by <.
-- This is Mathlib's `List.Pairwise` specialized to `<` on `Int`.
def StrictlyIncreasing (s : List Int) : Prop :=
  s.Pairwise (fun a b => a < b)

-- `s` is a strictly increasing subsequence of `nums`.
-- We use Mathlib's `List.Sublist` (a.k.a. `Sublist`, order-preserving deletion).
def IsStrictIncSubseq (s : List Int) (nums : List Int) : Prop :=
  List.Sublist s nums ∧ StrictlyIncreasing s

-- No preconditions: any integer list is allowed.
def precondition (nums : List Int) : Prop :=
  True

-- `result` is the maximum length of any strictly increasing subsequence.
-- We specify this via:
-- 1) Achievability: there exists a strictly increasing subsequence of length `result`.
-- 2) Maximality: every strictly increasing subsequence has length ≤ `result`.
def postcondition (nums : List Int) (result : Nat) : Prop :=
  (∃ s : List Int, IsStrictIncSubseq s nums ∧ s.length = result) ∧
  (∀ s : List Int, IsStrictIncSubseq s nums → s.length ≤ result)
end Specs

section Impl
method LongestIncreasingSubsequenceLength (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  -- Placeholder body only
  pure 0

prove_correct LongestIncreasingSubsequenceLength by sorry
end Impl

section TestCases
-- Test case 1: typical mixed list
-- LIS: [2,3,7,101] has length 4
-- nums = [10,9,2,5,3,7,101,18]
def test1_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test1_Expected : Nat := 4

-- Test case 2: empty list
-- LIS length = 0
def test2_nums : List Int := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list
-- LIS length = 1
def test3_nums : List Int := [42]
def test3_Expected : Nat := 1

-- Test case 4: strictly increasing already
-- LIS length = length of list
def test4_nums : List Int := [1, 2, 3, 4, 5]
def test4_Expected : Nat := 5

-- Test case 5: strictly decreasing
-- LIS length = 1
def test5_nums : List Int := [5, 4, 3, 2, 1]
def test5_Expected : Nat := 1

-- Test case 6: all equal elements (duplicates prevent strict increase)
-- LIS length = 1 (for any nonempty list)
def test6_nums : List Int := [7, 7, 7, 7]
def test6_Expected : Nat := 1

-- Test case 7: includes negative numbers
-- One LIS is [-3, -2, 0, 1] length 4
def test7_nums : List Int := [-3, -1, -2, 0, 1]
def test7_Expected : Nat := 4

-- Test case 8: duplicates interleaved
-- One LIS is [1,2,3] length 3
def test8_nums : List Int := [1, 2, 2, 2, 3]
def test8_Expected : Nat := 3

-- Test case 9: classic LIS example
-- One LIS is [0,2,6,9,11,15] length 6
def test9_nums : List Int := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
def test9_Expected : Nat := 6

-- Recommend to validate: empty input, duplicates, strictly decreasing
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Nat) :
  result ≠ test3_Expected →
  ¬ postcondition test3_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
