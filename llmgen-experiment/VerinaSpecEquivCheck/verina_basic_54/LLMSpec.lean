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
    MinAbsDiffBetweenSortedArrays: minimum absolute difference between any element of two sorted nonempty integer arrays.
    Natural language breakdown:
    1. Input consists of two arrays `a` and `b` of integers (`Int`).
    2. Both arrays are non-empty.
    3. Both arrays are sorted in non-decreasing order.
    4. Consider all pairs of indices (i, j) where i is a valid index into `a` and j is a valid index into `b`.
    5. For each pair, compute the absolute difference |a[i] - b[j]|.
    6. The output is a natural number (`Nat`) equal to the minimum of these absolute differences.
    7. The result must be achievable by at least one such pair, and must be less than or equal to every such absolute difference.
-/

section Specs
-- Helper: non-decreasing sortedness (allows equal neighbors)
def isSortedND (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: absolute difference as a natural number
-- `Int.natAbs` is the nonnegative absolute value of an integer, returned as `Nat`.
def absDiffNat (x : Int) (y : Int) : Nat :=
  Int.natAbs (x - y)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧
  b.size > 0 ∧
  isSortedND a ∧
  isSortedND b

def postcondition (a : Array Int) (b : Array Int) (result : Nat) : Prop :=
  -- Achievability: the minimum value is realized by some pair (i, j)
  (∃ (i : Nat), i < a.size ∧ ∃ (j : Nat), j < b.size ∧ result = absDiffNat a[i]! b[j]!) ∧
  -- Minimality: result is <= every pairwise absolute difference
  (∀ (i : Nat), i < a.size → ∀ (j : Nat), j < b.size → result ≤ absDiffNat a[i]! b[j]!)
end Specs

section Impl
method MinAbsDiffBetweenSortedArrays (a : Array Int) (b : Array Int)
  return (result : Nat)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: basic sorted arrays with a clear closest pair
-- a = [1, 3, 11, 15], b = [8, 19, 23, 127, 235] -> min |11-8| = 3

def test1_a : Array Int := #[1, 3, 11, 15]
def test1_b : Array Int := #[8, 19, 23, 127, 235]
def test1_Expected : Nat := 3

-- Test case 2: singleton arrays equal -> difference 0

def test2_a : Array Int := #[5]
def test2_b : Array Int := #[5]
def test2_Expected : Nat := 0

-- Test case 3: singleton arrays consecutive values including 0 and 1

def test3_a : Array Int := #[0]
def test3_b : Array Int := #[1]
def test3_Expected : Nat := 1

-- Test case 4: includes negative values
-- closest is -5 and -6 -> 1

def test4_a : Array Int := #[-10, -5, 0]
def test4_b : Array Int := #[-6, 7]
def test4_Expected : Nat := 1

-- Test case 5: duplicates in a and exact match in b -> 0

def test5_a : Array Int := #[1, 2, 2, 2, 3]
def test5_b : Array Int := #[2]
def test5_Expected : Nat := 0

-- Test case 6: far apart ranges
-- min |3 - 100| = 97

def test6_a : Array Int := #[1, 2, 3]
def test6_b : Array Int := #[100]
def test6_Expected : Nat := 97

-- Test case 7: large values; closest around 1_000_000
-- min |1_000_000 - 999_999| = 1

def test7_a : Array Int := #[0, 1000000]
def test7_b : Array Int := #[999999]
def test7_Expected : Nat := 1

-- Test case 8: symmetric around zero with -1 and 1 -> 2

def test8_a : Array Int := #[-1]
def test8_b : Array Int := #[1]
def test8_Expected : Nat := 2

-- Test case 9: interleaved ranges, multiple near matches -> 1

def test9_a : Array Int := #[1, 4, 7, 10]
def test9_b : Array Int := #[2, 3, 11]
def test9_Expected : Nat := 1
end TestCases
