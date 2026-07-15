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
    SwapFirstLast: Swap the first and last elements of a non-empty array of integers.
    Natural language breakdown:
    1. Input is an array `a` of integers.
    2. The input array is assumed to be non-empty.
    3. The output is a new array `result` with the same length as `a`.
    4. If the array length is 1, the output equals the input (the only element is both first and last).
    5. If the array length is at least 2:
       a. `result[0]` equals the last element of `a`.
       b. `result[last]` equals the first element of `a`.
       c. Every element strictly between first and last keeps its original value.
-/

section Specs
-- Helper: the last valid index of a non-empty array
-- For a.size > 0, `a.size - 1` is the index of the last element.
def lastIdx (a : Array Int) : Nat :=
  a.size - 1

-- Precondition: array is non-empty
-- Using a decidable numeric comparison (good for SMT and computation).
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: result has same size, first/last swapped, middle unchanged.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (a.size = 1 → result[0]! = a[0]!) ∧
  (a.size ≥ 2 →
    result[0]! = a[lastIdx a]! ∧
    result[lastIdx a]! = a[0]! ∧
    (∀ (i : Nat), i < a.size → i ≠ 0 → i ≠ lastIdx a → result[i]! = a[i]!))
end Specs

section Impl
method SwapFirstLast (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure a  -- placeholder body

prove_correct SwapFirstLast by sorry
end Impl

section TestCases
-- Test case 1: typical length 4
-- [1,2,3,4] -> [4,2,3,1]
def test1_a : Array Int := #[1, 2, 3, 4]
def test1_Expected : Array Int := #[4, 2, 3, 1]

-- Test case 2: length 1 (degenerate non-empty)
-- [7] -> [7]
def test2_a : Array Int := #[7]
def test2_Expected : Array Int := #[7]

-- Test case 3: length 2 (only swap)
-- [10,20] -> [20,10]
def test3_a : Array Int := #[10, 20]
def test3_Expected : Array Int := #[20, 10]

-- Test case 4: includes 0 and negatives
-- [0,-1,5] -> [5,-1,0]
def test4_a : Array Int := #[0, -1, 5]
def test4_Expected : Array Int := #[5, -1, 0]

-- Test case 5: all equal
-- [3,3,3,3,3] -> unchanged
-- (swap doesn't change due to equality)
def test5_a : Array Int := #[3, 3, 3, 3, 3]
def test5_Expected : Array Int := #[3, 3, 3, 3, 3]

-- Test case 6: already has same first/last but different middle
-- [9,1,2,9] -> unchanged
-- (swapping identical ends leaves array equal)
def test6_a : Array Int := #[9, 1, 2, 9]
def test6_Expected : Array Int := #[9, 1, 2, 9]

-- Test case 7: longer array
-- [1,2,3,4,5,6] -> [6,2,3,4,5,1]
def test7_a : Array Int := #[1, 2, 3, 4, 5, 6]
def test7_Expected : Array Int := #[6, 2, 3, 4, 5, 1]

-- Test case 8: boundary-like values in Int
-- [-10,0,10] -> [10,0,-10]
def test8_a : Array Int := #[-10, 0, 10]
def test8_Expected : Array Int := #[10, 0, -10]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Array Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
