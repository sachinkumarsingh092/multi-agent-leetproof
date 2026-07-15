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
    LongestIncreasingSubsequenceLength: find the length of the longest strictly increasing subsequence of an array.

    Natural language breakdown:
    1. Input is an array a of integers.
    2. A subsequence is determined by choosing some indices of a in strictly increasing order.
    3. The chosen elements must be strictly increasing in value (each is < the next).
    4. The output is the maximum possible length among all strictly increasing subsequences.
    5. The returned length is an integer (Int) and must be nonnegative.
    6. Edge cases:
       a. If a is empty, the result is 0.
       b. If a is nonempty, the result is at least 1.
       c. Equal adjacent values do not count as increasing (strictness).
-/

section Specs
-- Indices are valid positions within the array.
def idxsInBounds (a : Array Int) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k < idxs.size → idxs[k]! < a.size

-- Indices are strictly increasing (preserve order of the subsequence).
def idxsStrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k + 1 < idxs.size → idxs[k]! < idxs[k + 1]!

-- Values picked by indices are strictly increasing.
def valsStrictlyIncreasing (a : Array Int) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat),
    k + 1 < idxs.size →
      a[idxs[k]!]! < a[idxs[k + 1]!]!

-- A strictly increasing subsequence (represented by its index array).
def isStrictIncSubseqByIdxs (a : Array Int) (idxs : Array Nat) : Prop :=
  idxsInBounds a idxs ∧ idxsStrictlyIncreasing idxs ∧ valsStrictlyIncreasing a idxs

-- No input restriction: LIS length exists for all arrays.
def precondition (a : Array Int) : Prop :=
  True

-- result is the maximum possible length of any strictly increasing subsequence.
def postcondition (a : Array Int) (result : Int) : Prop :=
  0 ≤ result ∧
  result ≤ Int.ofNat a.size ∧
  (∃ (idxs : Array Nat), isStrictIncSubseqByIdxs a idxs ∧ Int.ofNat idxs.size = result) ∧
  (∀ (idxs : Array Nat), isStrictIncSubseqByIdxs a idxs → Int.ofNat idxs.size ≤ result)
end Specs

section Impl
method LongestIncreasingSubsequenceLength (a : Array Int)
  return (result : Int)
  require precondition a
  ensures postcondition a result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: empty array
def test1_a : Array Int := #[]
def test1_Expected : Int := 0

-- Test case 2: singleton array
def test2_a : Array Int := #[5]
def test2_Expected : Int := 1

-- Test case 3: already strictly increasing
def test3_a : Array Int := #[1, 2, 3, 4]
def test3_Expected : Int := 4

-- Test case 4: strictly decreasing
def test4_a : Array Int := #[4, 3, 2, 1]
def test4_Expected : Int := 1

-- Test case 5: small mixed order
def test5_a : Array Int := #[3, 1, 2]
def test5_Expected : Int := 2

-- Test case 6: all equal values (strictly increasing subsequence has length 1 if nonempty)
def test6_a : Array Int := #[1, 1, 1]
def test6_Expected : Int := 1

-- Test case 7: includes negative numbers
def test7_a : Array Int := #[-1, 0, 1]
def test7_Expected : Int := 3

-- Test case 8: classic LIS example
def test8_a : Array Int := #[10, 9, 2, 5, 3, 7, 101, 18]
def test8_Expected : Int := 4

-- Test case 9: larger classic example
def test9_a : Array Int := #[0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
def test9_Expected : Int := 6
end TestCases
