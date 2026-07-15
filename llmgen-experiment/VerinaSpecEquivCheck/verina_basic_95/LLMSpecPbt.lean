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
    SwapArrayElements: swap two elements of an integer array at given indices
    Natural language breakdown:
    1. We are given an array `arr` of integers and two indices `i` and `j` (0-indexed).
    2. Both indices are assumed to be non-negative and within the bounds of the array.
    3. The result is an array with the same size as `arr`.
    4. The element originally at index `i` appears at index `j` in the result.
    5. The element originally at index `j` appears at index `i` in the result.
    6. Every index other than `i` and `j` keeps the same element as in the input array.
-/

section Specs
-- Helper: convert an Int index (assumed nonnegative) to a Nat index.
def idx (k : Int) : Nat := Int.toNat k

-- Helper: the pointwise characterization of swapping indices i and j in arr.
def swapValueAt (arr : Array Int) (iN : Nat) (jN : Nat) (k : Nat) : Int :=
  if k = iN then arr[jN]!
  else if k = jN then arr[iN]!
  else arr[k]!

-- Preconditions: indices are non-negative and within array bounds.
def precondition (arr : Array Int) (i : Int) (j : Int) : Prop :=
  (0 ≤ i) ∧ (0 ≤ j) ∧ (idx i < arr.size) ∧ (idx j < arr.size)

-- Postconditions: result has same size and matches a swap at i and j.
def postcondition (arr : Array Int) (i : Int) (j : Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ k : Nat, k < arr.size →
    result[k]! = swapValueAt arr (idx i) (idx j) k)
end Specs

section Impl
method SwapArrayElements (arr : Array Int) (i : Int) (j : Int)
  return (result : Array Int)
  require precondition arr i j
  ensures postcondition arr i j result
  do
  pure arr  -- placeholder body

prove_correct SwapArrayElements by sorry
end Impl

section TestCases
-- Test case 1: swap middle and end in a length-3 array
-- arr = [1,2,3], i=1, j=2  => [1,3,2]
def test1_arr : Array Int := #[1, 2, 3]
def test1_i : Int := 1
def test1_j : Int := 2
def test1_Expected : Array Int := #[1, 3, 2]

-- Test case 2: swap first and last in a length-3 array
-- [10,20,30], i=0, j=2 => [30,20,10]
def test2_arr : Array Int := #[10, 20, 30]
def test2_i : Int := 0
def test2_j : Int := 2
def test2_Expected : Array Int := #[30, 20, 10]

-- Test case 3: swap adjacent elements in a length-2 array
-- [5,6], i=0, j=1 => [6,5]
def test3_arr : Array Int := #[5, 6]
def test3_i : Int := 0
def test3_j : Int := 1
def test3_Expected : Array Int := #[6, 5]

-- Test case 4: swap an index with itself (no-op)
-- [7,8,9], i=1, j=1 => [7,8,9]
def test4_arr : Array Int := #[7, 8, 9]
def test4_i : Int := 1
def test4_j : Int := 1
def test4_Expected : Array Int := #[7, 8, 9]

-- Test case 5: single-element array, only valid index 0
-- [42], i=0, j=0 => [42]
def test5_arr : Array Int := #[42]
def test5_i : Int := 0
def test5_j : Int := 0
def test5_Expected : Array Int := #[42]

-- Test case 6: swap where one index is last (boundary)
-- [0,1,2,3], i=3, j=1 => [0,3,2,1]
def test6_arr : Array Int := #[0, 1, 2, 3]
def test6_i : Int := 3
def test6_j : Int := 1
def test6_Expected : Array Int := #[0, 3, 2, 1]

-- Test case 7: array with negative and positive values
-- [-1,0,1], i=0, j=2 => [1,0,-1]
def test7_arr : Array Int := #[-1, 0, 1]
def test7_i : Int := 0
def test7_j : Int := 2
def test7_Expected : Array Int := #[1, 0, -1]

-- Test case 8: larger array, swap two interior indices
-- [2,4,6,8,10], i=1, j=3 => [2,8,6,4,10]
def test8_arr : Array Int := #[2, 4, 6, 8, 10]
def test8_i : Int := 1
def test8_j : Int := 3
def test8_Expected : Array Int := #[2, 8, 6, 4, 10]

-- Test case 9: swap first with itself while other elements exist
-- [11,22], i=0, j=0 => [11,22]
def test9_arr : Array Int := #[11, 22]
def test9_i : Int := 0
def test9_j : Int := 0
def test9_Expected : Array Int := #[11, 22]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_arr test9_i test9_j result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
