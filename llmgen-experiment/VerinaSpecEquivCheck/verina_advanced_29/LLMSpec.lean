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
    LongestGoodSubarrayLength: compute the maximum length of a contiguous non-empty subarray in which every value appears at most k times.
    Natural language breakdown:
    1. We are given an input list nums of natural numbers and a natural number k.
    2. The frequency of a value x in a list is the number of occurrences of x in that list.
    3. A list (subarray) is good if every value that appears in it occurs at most k times.
    4. A subarray is a contiguous, non-empty slice of nums.
    5. The result is the maximum length among all good subarrays of nums.
    6. If nums is empty, there is no non-empty subarray, so the maximum good subarray length is 0.
    7. Input constraint: k is positive (k > 0).
-/

section Specs
-- A subarray of nums is represented as (nums.drop start).take len.
-- We treat it as valid when len > 0 and start + len ≤ nums.length.
def IsValidSlice (nums : List Nat) (start : Nat) (len : Nat) : Prop :=
  len > 0 ∧ start + len ≤ nums.length

-- A slice is good when every element in it occurs at most k times within that slice.
-- We quantify only over values that appear in the slice (guarded by membership).
def GoodSlice (slice : List Nat) (k : Nat) : Prop :=
  ∀ (x : Nat), x ∈ slice → slice.count x ≤ k

-- Preconditions
-- k must be positive.
def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0

-- Postconditions
-- 1. result is within bounds.
-- 2. If nums is empty, result is 0.
-- 3. If nums is non-empty, there exists a good slice achieving length = result.
-- 4. result is maximal: every good slice length is ≤ result.
def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=
  result ≤ nums.length ∧
  ((nums = []) → result = 0) ∧
  ((nums ≠ []) →
    (∃ (start : Nat) (len : Nat),
      IsValidSlice nums start len ∧
      len = result ∧
      GoodSlice ((nums.drop start).take len) k)) ∧
  (∀ (start : Nat) (len : Nat),
    IsValidSlice nums start len →
    GoodSlice ((nums.drop start).take len) k →
    len ≤ result)
end Specs

section Impl
method LongestGoodSubarrayLength (nums : List Nat) (k : Nat)
  return (result : Nat)
  require precondition nums k
  ensures postcondition nums k result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: all elements distinct, k = 1, whole array is good
def test1_nums : List Nat := [1, 2, 3]
def test1_k : Nat := 1
def test1_Expected : Nat := 3

-- Test case 2: all same, k = 1
def test2_nums : List Nat := [1, 1, 1]
def test2_k : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: all same, k = 2
def test3_nums : List Nat := [1, 1, 1]
def test3_k : Nat := 2
def test3_Expected : Nat := 2

-- Test case 4: alternating values, k = 2
def test4_nums : List Nat := [1, 2, 1, 2, 1, 2]
def test4_k : Nat := 2
def test4_Expected : Nat := 4

-- Test case 5: empty input list
def test5_nums : List Nat := []
def test5_k : Nat := 1
def test5_Expected : Nat := 0

-- Test case 6: includes 0, k = 3
def test6_nums : List Nat := [0, 0, 0, 0]
def test6_k : Nat := 3
def test6_Expected : Nat := 3

-- Test case 7: singleton list, large k
def test7_nums : List Nat := [5]
def test7_k : Nat := 10
def test7_Expected : Nat := 1

-- Test case 8: mixed frequencies, k = 2
def test8_nums : List Nat := [1, 2, 2, 3, 3, 3]
def test8_k : Nat := 2
def test8_Expected : Nat := 5

-- Test case 9: multiple repeats, k = 2
def test9_nums : List Nat := [1, 1, 2, 2, 2, 1]
def test9_k : Nat := 2
def test9_Expected : Nat := 4
end TestCases
