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
    KthElement1Based: Return the k-th element of an integer array using 1-based indexing.
    Natural language breakdown:
    1. The input is an array `arr` of integers and a natural number `k`.
    2. Indexing is 1-based: position 1 refers to the first element of the array.
    3. The input `k` is assumed valid: 1 ≤ k and k ≤ arr.size.
    4. The array is assumed non-empty.
    5. The output is the element stored in the array at zero-based index (k - 1).
-/

section Specs
-- Helper: the corresponding 0-based index for a 1-based position.
-- Note: this is only meaningful when k ≥ 1.
def idx0 (k : Nat) : Nat := k - 1

def precondition (arr : Array Int) (k : Nat) : Prop :=
  arr.size > 0 ∧ 1 ≤ k ∧ k ≤ arr.size

def postcondition (arr : Array Int) (k : Nat) (result : Int) : Prop :=
  -- Because k is within [1, arr.size], (k-1) is a valid 0-based index.
  result = arr[idx0 k]!
end Specs

section Impl
method KthElement1Based (arr : Array Int) (k : Nat)
  return (result : Int)
  require precondition arr k
  ensures postcondition arr k result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: simple example, pick the 3rd element
-- arr = [10, 20, 30, 40], k = 3 -> 30

def test1_arr : Array Int := #[10, 20, 30, 40]
def test1_k : Nat := 3
def test1_Expected : Int := 30

-- Test case 2: boundary k = 1 (first element)
def test2_arr : Array Int := #[7, 8, 9]
def test2_k : Nat := 1
def test2_Expected : Int := 7

-- Test case 3: boundary k = arr.size (last element)
def test3_arr : Array Int := #[-1, 0, 1]
def test3_k : Nat := 3

def test3_Expected : Int := 1

-- Test case 4: singleton array, only valid k = 1
def test4_arr : Array Int := #[42]
def test4_k : Nat := 1
def test4_Expected : Int := 42

-- Test case 5: size 2 array, choose second element

def test5_arr : Array Int := #[5, 6]
def test5_k : Nat := 2
def test5_Expected : Int := 6

-- Test case 6: array with negative numbers, choose middle

def test6_arr : Array Int := #[-10, -20, -30, -40, -50]
def test6_k : Nat := 4
def test6_Expected : Int := -40

-- Test case 7: array containing zeros, choose a zero

def test7_arr : Array Int := #[3, 0, 4, 0, 5]
def test7_k : Nat := 2
def test7_Expected : Int := 0

-- Test case 8: larger array, typical interior index

def test8_arr : Array Int := #[100, 200, 300, 400, 500, 600]
def test8_k : Nat := 5
def test8_Expected : Int := 500
end TestCases
