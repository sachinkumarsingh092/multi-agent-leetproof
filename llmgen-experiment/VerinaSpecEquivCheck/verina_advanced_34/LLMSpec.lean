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
    LongestIncreasingSubsequenceLength: compute the length of the longest strictly increasing subsequence of a list of integers.

    Natural language breakdown:
    1. Input is a list of integers nums.
    2. A subsequence is obtained by deleting zero or more elements from nums without changing the order of the remaining elements.
    3. A subsequence is strictly increasing if every earlier element is strictly less than every later element.
    4. The desired output is the maximum possible length among all strictly increasing subsequences of nums.
    5. The empty list is a subsequence of any list, so the result is always defined and is always nonnegative.
    6. If nums is empty, the longest strictly increasing subsequence has length 0.
-/

section Specs
-- A list is strictly increasing iff every element is strictly less than every later element.
-- `List.Pairwise r xs` means `r` holds for every pair of elements with increasing position.
def StrictlyIncreasing (xs : List Int) : Prop :=
  xs.Pairwise (fun a => fun b => a < b)

-- `k` is the length (Nat) of a longest strictly increasing subsequence of `nums`.
-- We use `List.Sublist` as the subsequence relation (delete elements, order preserved).
-- Note: `[]` is a sublist of any list, so existence is always satisfied with `k = 0`.
def IsLISLengthNat (nums : List Int) (k : Nat) : Prop :=
  (∃ s : List Int, List.Sublist s nums ∧ StrictlyIncreasing s ∧ s.length = k) ∧
  (∀ t : List Int, List.Sublist t nums → StrictlyIncreasing t → t.length ≤ k)

-- No preconditions: any integer list is allowed.
def precondition (nums : List Int) : Prop :=
  True

-- The returned integer is the natural number `k` (encoded via `Int.ofNat`) such that:
-- 1) there exists a strictly increasing subsequence of length `k`, and
-- 2) no strictly increasing subsequence is longer than `k`.
def postcondition (nums : List Int) (result : Int) : Prop :=
  ∃ k : Nat,
    result = Int.ofNat k ∧
    IsLISLengthNat nums k
end Specs

section Impl
method LongestIncreasingSubsequenceLength (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: empty list
-- LIS length is 0

def test1_nums : List Int := []
def test1_Expected : Int := 0

-- Test case 2: singleton list
-- LIS length is 1

def test2_nums : List Int := [42]
def test2_Expected : Int := 1

-- Test case 3: strictly decreasing list
-- LIS length is 1

def test3_nums : List Int := [3, 2, 1]
def test3_Expected : Int := 1

-- Test case 4: strictly increasing list
-- LIS length is the full length

def test4_nums : List Int := [1, 2, 3]
def test4_Expected : Int := 3

-- Test case 5: typical mixed example
-- One LIS is [2,3,7,101]

def test5_nums : List Int := [10, 9, 2, 5, 3, 7, 101, 18]
def test5_Expected : Int := 4

-- Test case 6: duplicates only (strictly increasing forbids equals)
-- LIS length is 1

def test6_nums : List Int := [2, 2, 2]
def test6_Expected : Int := 1

-- Test case 7: includes negative values
-- Entire list is strictly increasing

def test7_nums : List Int := [-1, 0, 1]
def test7_Expected : Int := 3

-- Test case 8: repeated and interleaved values
-- One LIS is [0,1,2,3]

def test8_nums : List Int := [0, 1, 0, 3, 2, 3]
def test8_Expected : Int := 4

-- Test case 9: another standard benchmark
-- One LIS is [4,8,9]

def test9_nums : List Int := [4, 10, 4, 3, 8, 9]
def test9_Expected : Int := 3

-- Recommend to validate: empty input, duplicates-only, mixed positive/negative
end TestCases
