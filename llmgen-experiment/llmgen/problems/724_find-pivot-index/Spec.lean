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
    724. Find Pivot Index: compute the leftmost index where the sum of elements strictly to the left
    equals the sum of elements strictly to the right; if none exists return -1.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. For an index `i`, define `leftSum(i)` as the sum of elements at indices `< i`.
    3. Define `rightSum(i)` as the sum of elements at indices `> i`.
    4. Index `i` is a pivot index iff `leftSum(i) = rightSum(i)`.
    5. If `i = 0`, then `leftSum(i) = 0` (empty left side); similarly if `i` is the last index,
       then `rightSum(i) = 0`.
    6. If at least one pivot index exists, return the smallest such index (the leftmost pivot).
    7. If no pivot index exists, return -1.
-/

section Specs
-- Sum of all elements of an Int array.
def arraySum (a : Array Int) : Int :=
  a.foldl (fun acc x => acc + x) 0

-- Sum of a half-open slice a[start, stop) using Array.extract.
-- If start ≥ stop, the extracted array is empty and the sum is 0.
def arraySumRange (a : Array Int) (start : Nat) (stop : Nat) : Int :=
  (a.extract start stop).foldl (fun acc x => acc + x) 0

-- Pivot predicate for a valid index i.
def isPivotIndex (nums : Array Int) (i : Nat) : Prop :=
  i < nums.size ∧
  arraySumRange nums 0 i = arraySumRange nums (i + 1) nums.size

-- Precondition: none.
def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ i : Nat, i < nums.size → ¬ isPivotIndex nums i)) ∨
  (∃ i : Nat,
      i < nums.size ∧
      result = Int.ofNat i ∧
      isPivotIndex nums i ∧
      (∀ j : Nat, j < i → ¬ isPivotIndex nums j))
end Specs

section Impl
method FindPivotIndex (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure (-1)  -- placeholder body

end Impl

section TestCases
-- Test case 1: example 1
-- nums = [1,7,3,6,5,6] => 3

def test1_nums : Array Int := #[1, 7, 3, 6, 5, 6]
def test1_Expected : Int := 3

-- Test case 2: example 2
-- nums = [1,2,3] => -1

def test2_nums : Array Int := #[1, 2, 3]
def test2_Expected : Int := (-1)

-- Test case 3: example 3
-- nums = [2,1,-1] => 0

def test3_nums : Array Int := #[2, 1, -1]
def test3_Expected : Int := 0

-- Test case 4: empty array => pivot does not exist => -1

def test4_nums : Array Int := #[]
def test4_Expected : Int := (-1)

-- Test case 5: singleton array => pivot at index 0

def test5_nums : Array Int := #[42]
def test5_Expected : Int := 0

-- Test case 6: pivot at last index (right sum = 0)
-- nums = [1,-1,0] => 2

def test6_nums : Array Int := #[1, -1, 0]
def test6_Expected : Int := 2

-- Test case 7: multiple pivots, must return leftmost
-- nums = [0,0,0] pivots at 0,1,2 => result 0

def test7_nums : Array Int := #[0, 0, 0]
def test7_Expected : Int := 0

-- Test case 8: typical with negatives, pivot in the middle
-- nums = [-1,-1,0,1,1,0] => pivot 2

def test8_nums : Array Int := #[-1, -1, 0, 1, 1, 0]
def test8_Expected : Int := 2

-- Test case 9: no pivot even though sums match nowhere
-- nums = [2,3,-2] => -1

def test9_nums : Array Int := #[2, 3, -2]
def test9_Expected : Int := (-1)
end TestCases
