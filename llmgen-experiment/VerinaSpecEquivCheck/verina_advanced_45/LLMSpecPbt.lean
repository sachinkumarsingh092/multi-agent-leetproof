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
    MaxSubarraySum: compute the maximum sum over all contiguous subarrays of a list of integers.

    Natural language breakdown:
    1. The input is a list of integers `xs` which may contain negative and positive values.
    2. A subarray is a contiguous segment of `xs`, determined by start index `i` and end index `j` with `i ≤ j`.
    3. The sum of a subarray is the sum of its elements.
    4. The function returns the maximum subarray sum among all (possibly empty) subarrays.
    5. The empty subarray is allowed and has sum 0.
    6. Therefore the returned value is always at least 0.
    7. If `xs` is empty, the only subarray is the empty one, so the result must be 0.
-/

section Specs
-- Sum of the subarray xs[i..j) (start inclusive, end exclusive).
-- This includes the empty subarray when i = j, whose sum is 0.
-- Indices are Nat; bounds are enforced in the postcondition.
def subarraySum (xs : List Int) (i : Nat) (j : Nat) : Int :=
  ((xs.drop i).take (j - i)).sum

def precondition (xs : List Int) : Prop :=
  True

-- The result is a maximum among all subarray sums (including empty subarrays),
-- and is achievable by some valid indices.
def postcondition (xs : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ (i : Nat) (j : Nat), i ≤ j ∧ j ≤ xs.length ∧ subarraySum xs i j = result) ∧
  (∀ (i : Nat) (j : Nat), i ≤ j ∧ j ≤ xs.length → subarraySum xs i j ≤ result)
end Specs

section Impl
method MaxSubarraySum (xs : List Int)
  return (result : Int)
  require precondition xs
  ensures postcondition xs result
  do
  pure 0

prove_correct MaxSubarraySum by sorry
end Impl

section TestCases
-- Test case 1: typical mixed list
-- Maximum subarray is [3,4] with sum 7.
def test1_xs : List Int := [1, -2, 3, 4, -1]
def test1_Expected : Int := 7

-- Test case 2: empty input => 0

def test2_xs : List Int := []
def test2_Expected : Int := 0

-- Test case 3: singleton positive

def test3_xs : List Int := [5]
def test3_Expected : Int := 5

-- Test case 4: singleton negative => choose empty subarray

def test4_xs : List Int := [-5]
def test4_Expected : Int := 0

-- Test case 5: all negative => 0

def test5_xs : List Int := [-2, -3, -1, -4]
def test5_Expected : Int := 0

-- Test case 6: all positive => sum of all

def test6_xs : List Int := [1, 2, 3, 4]
def test6_Expected : Int := 10

-- Test case 7: includes zeros and negatives
-- Best is [0,3,0] => 3.
def test7_xs : List Int := [0, -1, 0, 3, 0, -2]
def test7_Expected : Int := 3

-- Test case 8: classic case with internal maximum
-- Best is [4,-1,2,1] => 6.
def test8_xs : List Int := [-2, 1, -3, 4, -1, 2, 1, -5, 4]
def test8_Expected : Int := 6

-- Test case 9: boundary with 0 and 1 length effects
-- Best is [1] => 1.
def test9_xs : List Int := [0, -1, 1, -1, 0]
def test9_Expected : Int := 1
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_xs result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
