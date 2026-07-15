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
    MaxSubarraySumLenDivK: maximum subarray sum whose length is divisible by k
    Natural language breakdown:
    1. Input is an integer array arr and an integer k with k > 1.
    2. A subarray is a contiguous segment specified by indices start and stop with 0 ≤ start < stop ≤ arr.size.
    3. The length of the subarray is (stop - start).
    4. A subarray is eligible when its length is divisible by k.
    5. The sum of a subarray is the sum of its elements.
    6. The output is the maximum value among sums of all eligible subarrays, but never negative: if all eligible sums
       are ≤ 0 or if there is no eligible subarray (including the case arr is empty), the output is 0.
-/

section Specs
-- Convert the (positive) Int k to Nat for divisibility over Nat lengths.
-- Precondition guarantees 2 ≤ k, so Int.toNat k is nonzero.
def kNat (k : Int) : Nat :=
  Int.toNat k

-- Sum of the subarray arr[start:stop] (stop exclusive).
-- We use Array.extract, together with explicit bounds in predicates, to model a subarray slice.
def subarraySum (arr : Array Int) (start : Nat) (stop : Nat) : Int :=
  (arr.extract start stop).sum

-- A non-empty, in-bounds subarray.
def validSubarray (arr : Array Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ arr.size

-- Length divisibility by k (with k viewed as a natural number).
def lenDivisibleByK (len : Nat) (k : Int) : Prop :=
  len % (kNat k) = 0

-- Candidate predicate: a valid non-empty subarray with length divisible by k.
def isCandidate (arr : Array Int) (k : Int) (start : Nat) (stop : Nat) : Prop :=
  validSubarray arr start stop ∧ lenDivisibleByK (stop - start) k

-- k must be larger than 1.
def precondition (arr : Array Int) (k : Int) : Prop :=
  2 ≤ k

-- result is the greatest nonnegative sum among all candidate subarrays; default 0.
def postcondition (arr : Array Int) (k : Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∀ (start : Nat) (stop : Nat), isCandidate arr k start stop → subarraySum arr start stop ≤ result) ∧
  (result = 0 ∨ ∃ (start : Nat) (stop : Nat), isCandidate arr k start stop ∧ subarraySum arr start stop = result)
end Specs

section Impl
method MaxSubarraySumLenDivK (arr : Array Int) (k : Int)
  return (result : Int)
  require precondition arr k
  ensures postcondition arr k result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical case, k = 2
-- Eligible lengths: 2, 4. Best is whole array sum 10.
def test1_arr : Array Int := #[1, 2, 3, 4]
def test1_k : Int := 2
def test1_Expected : Int := 10

-- Test case 2: empty array => no non-empty eligible subarray
def test2_arr : Array Int := #[]
def test2_k : Int := 3
def test2_Expected : Int := 0

-- Test case 3: all candidate sums negative => default 0
def test3_arr : Array Int := #[-1, -2, -3, -4]
def test3_k : Int := 2
def test3_Expected : Int := 0

-- Test case 4: singleton array, no length divisible by 2 (non-empty) => 0
def test4_arr : Array Int := #[5]
def test4_k : Int := 2
def test4_Expected : Int := 0

-- Test case 5: k = 3 with mixed numbers
-- Best eligible length-3 subarray is [-1,2,3] sum 4.
def test5_arr : Array Int := #[2, -1, 2, 3, -9, 4]
def test5_k : Int := 3
def test5_Expected : Int := 4

-- Test case 6: zeros only, candidates exist but max sum is 0
def test6_arr : Array Int := #[0, 0, 0, 0]
def test6_k : Int := 2
def test6_Expected : Int := 0

-- Test case 7: best is length 4 divisible by 2
def test7_arr : Array Int := #[10, -1, -1, 10]
def test7_k : Int := 2
def test7_Expected : Int := 18

-- Test case 8: best is length 4 subarray [3,4,-1,2] sum 8
def test8_arr : Array Int := #[1, -2, 3, 4, -1, 2]
def test8_k : Int := 2
def test8_Expected : Int := 8

-- Test case 9: k larger than array size => no eligible non-empty subarray
def test9_arr : Array Int := #[1, 2, 3]
def test9_k : Int := 4
def test9_Expected : Int := 0
end TestCases
