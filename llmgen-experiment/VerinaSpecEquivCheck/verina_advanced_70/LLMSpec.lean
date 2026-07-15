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
    MinAdjacentSwapsSemiOrdered: compute the minimum number of adjacent swaps needed to make a permutation semi-ordered.
    Natural language breakdown:
    1. The input is a list `nums` of length `n` that is a permutation of the integers 1,2,...,n.
    2. An operation consists of swapping two adjacent elements.
    3. A list is semi-ordered if its first element is 1 and its last element is n.
    4. The goal is to compute the minimum number of adjacent swaps needed to make the list semi-ordered.
    5. In a permutation, the minimum number of adjacent swaps to move a distinguished element to a position equals the distance in indices.
    6. Let `pos1` be the index of value 1 and `posN` be the index of value n.
    7. Moving 1 to the front costs `pos1` swaps.
    8. Moving n to the end costs `(n-1 - posN)` swaps, but if 1 must cross over n (i.e., pos1 > posN), the total is reduced by 1 because one swap serves both movements.
    9. Therefore the minimal swap count equals `pos1 + (n-1 - posN) - (if pos1 > posN then 1 else 0)`.
-/

section Specs
-- Helper: the intended size n as an Int.
def nVal (nums : List Int) : Int :=
  Int.ofNat nums.length

-- Helper: index of a value, using boolean equality.
-- For valid inputs (permutation of 1..n), the searched elements are present.
def indexOfInt (a : Int) (nums : List Int) : Nat :=
  nums.findIdx (fun x => x == a)

-- Helper: range constraint for permutation elements: every element is in [1..n].
def elemsInRange (nums : List Int) : Prop :=
  ∀ (i : Nat), i < nums.length →
    (1 ≤ nums[i]!) ∧ (nums[i]! ≤ nVal nums)

-- Helper: the swap-count formula (as Nat).
def swapCountNat (nums : List Int) : Nat :=
  let pos1 : Nat := indexOfInt 1 nums
  let posN : Nat := indexOfInt (nVal nums) nums
  let cost1 : Nat := pos1
  let costN : Nat := (nums.length - 1) - posN
  let overlap : Nat := if pos1 > posN then 1 else 0
  cost1 + costN - overlap

-- Preconditions
-- We keep them mostly decidable and avoid heavy permutation machinery.
-- We assume:
-- 1) n = nums.length is at least 1
-- 2) all elements are within [1..n]
-- 3) no duplicates
-- 4) 1 and n actually occur (captured via findIdx bounds)
def precondition (nums : List Int) : Prop :=
  nums.length ≥ 1 ∧
  elemsInRange nums ∧
  nums.Nodup ∧
  indexOfInt 1 nums < nums.length ∧
  indexOfInt (nVal nums) nums < nums.length

-- Postcondition
-- The result is exactly the minimal number of adjacent swaps, characterized by the index-based formula.
-- We return it as an Int equal to the Nat formula coerced to Int.
def postcondition (nums : List Int) (result : Int) : Prop :=
  result = Int.ofNat (swapCountNat nums)
end Specs

section Impl
method MinAdjacentSwapsSemiOrdered (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical permutation
def test1_nums : List Int := [2, 1, 4, 3]
def test1_Expected : Int := 2

-- Test case 2: already semi-ordered
def test2_nums : List Int := [1, 2, 3, 4]
def test2_Expected : Int := 0

-- Test case 3: n = 1 (degenerate permutation)
def test3_nums : List Int := [1]
def test3_Expected : Int := 0

-- Test case 4: n = 2 already semi-ordered
def test4_nums : List Int := [1, 2]
def test4_Expected : Int := 0

-- Test case 5: n = 2 reversed
def test5_nums : List Int := [2, 1]
def test5_Expected : Int := 1

-- Test case 6: 1 needs one swap, n already at end
def test6_nums : List Int := [3, 1, 2, 4]
def test6_Expected : Int := 1

-- Test case 7: 1 is after n (overlap subtraction applies)
def test7_nums : List Int := [3, 2, 1]
def test7_Expected : Int := 3

-- Test case 8: n at front, 1 at end
def test8_nums : List Int := [4, 2, 3, 1]
def test8_Expected : Int := 5

-- Test case 9: 1 in middle, n at end
def test9_nums : List Int := [2, 3, 4, 1, 5]
def test9_Expected : Int := 3
end TestCases
