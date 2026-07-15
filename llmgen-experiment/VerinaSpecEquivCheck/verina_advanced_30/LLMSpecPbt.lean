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
    LongestStrictlyIncreasingContiguousSubarrayLength: compute the length of the longest strictly increasing contiguous subarray in a list of integers.

    Natural language breakdown:
    1. Input is a list of integers `nums`.
    2. A contiguous subarray is determined by a start index `s` and a length `len` such that `s + len ≤ nums.length`.
    3. A contiguous subarray of length `len` starting at `s` is strictly increasing if for every adjacent pair inside the segment,
       the later element is strictly greater than the earlier one.
    4. The output is a natural number `result`.
    5. If `nums` is empty, the result is 0.
    6. If `nums` is non-empty, the result is between 1 and `nums.length`.
    7. There must exist some strictly increasing contiguous segment in `nums` whose length is exactly `result`.
    8. No strictly increasing contiguous segment in `nums` may have length greater than `result`.
-/

section Specs
-- A segment of `nums` starting at index `start` with length `len` is strictly increasing
-- if every adjacent pair within the segment increases.
-- This predicate is only intended to be used when `start + len ≤ nums.length`.
def StrictIncSegment (nums : List Int) (start : Nat) (len : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < len → nums.get! (start + i) < nums.get! (start + i + 1)

-- Precondition: no restrictions.
def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list case
  (nums = [] → result = 0) ∧
  -- Non-empty list case bounds
  (nums ≠ [] → 1 ≤ result ∧ result ≤ nums.length) ∧
  -- Achievability: there exists a strictly increasing segment of length `result`
  (∃ (start : Nat), start + result ≤ nums.length ∧ StrictIncSegment nums start result) ∧
  -- Maximality: any strictly increasing segment length is bounded by `result`
  (∀ (start : Nat) (len : Nat),
      start + len ≤ nums.length →
      StrictIncSegment nums start len →
      len ≤ result)
end Specs

section Impl
method LongestIncRunLen (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0  -- placeholder body

prove_correct LongestIncRunLen by sorry
end Impl

section TestCases
-- Test case 1: empty list
def test1_nums : List Int := []
def test1_Expected : Nat := 0

-- Test case 2: singleton list
def test2_nums : List Int := [5]
def test2_Expected : Nat := 1

-- Test case 3: all equal elements
def test3_nums : List Int := [7, 7, 7, 7]
def test3_Expected : Nat := 1

-- Test case 4: strictly increasing whole list
def test4_nums : List Int := [1, 2, 3, 4, 5]
def test4_Expected : Nat := 5

-- Test case 5: strictly decreasing whole list
def test5_nums : List Int := [5, 4, 3, 2, 1]
def test5_Expected : Nat := 1

-- Test case 6: mixed with a longest run in the middle
def test6_nums : List Int := [1, 2, 2, 3, 4, 1]
def test6_Expected : Nat := 3  -- [2,3,4]

-- Test case 7: includes negative numbers, longest run crosses them
def test7_nums : List Int := [-3, -2, -1, -1, 0, 1]
def test7_Expected : Nat := 3  -- [-3,-2,-1]

-- Test case 8: long increasing suffix
def test8_nums : List Int := [10, 9, 8, 1, 2, 3, 4]
def test8_Expected : Nat := 4  -- [1,2,3,4]

-- Test case 9: multiple increasing runs, choose the maximal
def test9_nums : List Int := [1, 3, 5, 4, 6, 8, 10, 2]
def test9_Expected : Nat := 4  -- [4,6,8,10]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
