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
    MaxSubarraySum: compute the maximum sum over all non-empty contiguous subarrays of a non-empty integer sequence.
    Natural language breakdown:
    1. The input is a list of integers `sequence`.
    2. A contiguous subarray is determined by two indices `start` and `stop` with `start < stop` and `stop ≤ sequence.length`.
    3. The elements of this subarray are exactly `sequence.drop start` truncated to length `stop - start`.
    4. The sum of a subarray is the integer sum of its elements.
    5. The output `result` must equal the sum of at least one non-empty contiguous subarray (achievability).
    6. The output `result` must be greater than or equal to the sum of every non-empty contiguous subarray (maximality).
    7. Since at least one number must be selected, the input list must be non-empty.
-/

section Specs
-- Helper: sum of a list of integers.
-- We use `foldl` to avoid relying on any particular `List.sum` import.
def listSum (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc + x) 0

-- Helper: contiguous subarray slice of `sequence` from `start` (inclusive) to `stop` (exclusive).
-- Intended use is with `start < stop` and `stop ≤ sequence.length`.
def subarraySlice (sequence : List Int) (start : Nat) (stop : Nat) : List Int :=
  (sequence.drop start).take (stop - start)

-- Helper: sum of a contiguous subarray slice.
def subarraySliceSum (sequence : List Int) (start : Nat) (stop : Nat) : Int :=
  listSum (subarraySlice sequence start stop)

-- Helper: (start, stop) denotes a valid non-empty contiguous subarray.
def isValidWindow (sequence : List Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ sequence.length

-- Preconditions
-- The input sequence must be non-empty.
def precondition (sequence : List Int) : Prop :=
  sequence.length > 0

-- Postconditions
-- `result` is the maximum sum among all non-empty contiguous subarrays.
def postcondition (sequence : List Int) (result : Int) : Prop :=
  (∃ (start : Nat) (stop : Nat),
      isValidWindow sequence start stop ∧
      subarraySliceSum sequence start stop = result) ∧
  (∀ (start : Nat) (stop : Nat),
      isValidWindow sequence start stop →
      subarraySliceSum sequence start stop ≤ result)
end Specs

section Impl
method MaxSubarraySum (sequence : List Int)
  return (result : Int)
  require precondition sequence
  ensures postcondition sequence result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: classic mixed example
-- Expected maximum subarray is [4, -1, 2, 1] with sum 6
-- (This is the standard example for the maximum-subarray problem.)
def test1_sequence : List Int := [-2, 1, -3, 4, -1, 2, 1, -5, 4]
def test1_Expected : Int := 6

-- Test case 2: single element (positive)
def test2_sequence : List Int := [5]
def test2_Expected : Int := 5

-- Test case 3: single element (negative)
def test3_sequence : List Int := [-7]
def test3_Expected : Int := -7

-- Test case 4: all negative elements
-- Must choose at least one element, so answer is the largest (least negative)
def test4_sequence : List Int := [-8, -3, -6, -2, -5, -4]
def test4_Expected : Int := -2

-- Test case 5: all positive elements (take entire list)
def test5_sequence : List Int := [1, 2, 3, 4]
def test5_Expected : Int := 10

-- Test case 6: includes zeros; best sum is 0 from a singleton [0]
def test6_sequence : List Int := [-1, 0, -2]
def test6_Expected : Int := 0

-- Test case 7: best window occurs at the end
-- Best is [4, 5] sum 9
def test7_sequence : List Int := [-2, -1, 4, 5]
def test7_Expected : Int := 9

-- Test case 8: alternating small gains/losses
-- Best is [2, -1, 2, -1, 2] sum 4
def test8_sequence : List Int := [2, -1, 2, -1, 2, -10]
def test8_Expected : Int := 4

-- Test case 9: many zeros; answer is 0
-- Any non-empty window has sum 0.
def test9_sequence : List Int := [0, 0, 0]
def test9_Expected : Int := 0

-- Recommend to validate: all-negative inputs, singleton inputs, zero-heavy inputs
end TestCases
