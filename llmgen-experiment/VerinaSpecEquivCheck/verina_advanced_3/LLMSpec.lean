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
    LCSLength: Find the length of the longest common subsequence of two input arrays.

    Natural language breakdown:
    1. We are given two arrays of integers, a and b.
    2. A subsequence of an array is obtained by selecting elements at strictly increasing indices.
    3. A common subsequence of a and b is an array s that is a subsequence of a and also a subsequence of b.
    4. The output is the length of the longest (maximum-length) common subsequence.
    5. If either input array is empty, the longest common subsequence length is 0.
    6. The result is always a non-negative integer.
-/

section Specs
-- Helper: strictly increasing indices for an index array.
def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (j : Nat), j + 1 < idxs.size → idxs[j]! < idxs[j + 1]!

-- Helper: s is a subsequence of arr, witnessed by an index array idxs.
def SubseqWitness (s : Array Int) (arr : Array Int) (idxs : Array Nat) : Prop :=
  idxs.size = s.size ∧
  StrictlyIncreasing idxs ∧
  (∀ (j : Nat), j < s.size → idxs[j]! < arr.size ∧ s[j]! = arr[idxs[j]!]!)

-- Helper: array subsequence relation.
def IsSubsequence (s : Array Int) (arr : Array Int) : Prop :=
  ∃ (idxs : Array Nat), SubseqWitness s arr idxs

-- Precondition: no restrictions on inputs.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition: result is the maximum possible length of any common subsequence.
-- Note: result is Int, but array sizes are Nat, so we relate them via Int.ofNat and result.toNat.
def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ (s : Array Int), IsSubsequence s a ∧ IsSubsequence s b ∧ result = Int.ofNat s.size) ∧
  (∀ (t : Array Int), IsSubsequence t a ∧ IsSubsequence t b → (Int.ofNat t.size) ≤ result)
end Specs

section Impl
method LCSLength (a : Array Int) (b : Array Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: both empty arrays
def test1_a : Array Int := #[]
def test1_b : Array Int := #[]
def test1_Expected : Int := 0

-- Test case 2: one empty, one non-empty
def test2_a : Array Int := #[1, 2, 3]
def test2_b : Array Int := #[]
def test2_Expected : Int := 0

-- Test case 3: singletons equal
def test3_a : Array Int := #[5]
def test3_b : Array Int := #[5]
def test3_Expected : Int := 1

-- Test case 4: singletons different
def test4_a : Array Int := #[5]
def test4_b : Array Int := #[6]
def test4_Expected : Int := 0

-- Test case 5: identical arrays
def test5_a : Array Int := #[1, 2, 3, 4]
def test5_b : Array Int := #[1, 2, 3, 4]
def test5_Expected : Int := 4

-- Test case 6: subsequence exists with skips
def test6_a : Array Int := #[1, 3, 4, 1, 2, 3]
def test6_b : Array Int := #[3, 4, 1, 2, 1, 3]
-- One LCS is [3,4,1,2,3] of length 5 is not possible here due to ordering; typical LCS length is 5? actually 5 is too large.
-- A valid LCS is [3,4,1,2,3] fails in b ordering (3,4,1,2,3 exists) and in a ordering (3 at idx1,4 idx2,1 idx3,2 idx4,3 idx5) works.
-- So length 5 is achievable.
def test6_Expected : Int := 5

-- Test case 7: repeated elements, ensure counting respects order
def test7_a : Array Int := #[1, 1, 1]
def test7_b : Array Int := #[1, 1]
def test7_Expected : Int := 2

-- Test case 8: no common elements
def test8_a : Array Int := #[1, 2, 3]
def test8_b : Array Int := #[4, 5, 6]
def test8_Expected : Int := 0

-- Test case 9: negatives and mixed order
def test9_a : Array Int := #[-1, 0, 1, 2]
def test9_b : Array Int := #[0, -1, 2, 1]
-- LCS length is 2, e.g. [0,2] or [-1,2]
def test9_Expected : Int := 2
end TestCases
