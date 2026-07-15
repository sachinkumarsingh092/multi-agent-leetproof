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
    ArrayElementwiseSum: compute the element-wise sum of two integer arrays of equal length.
    Natural language breakdown:
    1. The inputs are two arrays `a` and `b` of integers.
    2. The inputs are required to have the same length.
    3. The output is a new array `result`.
    4. The output has the same size as `a` (and therefore also as `b`).
    5. For every valid index `i`, the element `result[i]` equals `a[i] + b[i]`.
-/

section Specs
-- Precondition: arrays must have equal size.
-- This matches the problem statement assumption and ensures index-wise correspondence.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

-- Postcondition: result has the same size and matches element-wise addition.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ (i : Nat), i < a.size → result[i]! = a[i]! + b[i]!
end Specs

section Impl
method ArrayElementwiseSum (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  -- Placeholder implementation only.
  pure (Array.replicate a.size 0)

prove_correct ArrayElementwiseSum by sorry
end Impl

section TestCases
-- Test case 1: typical small arrays
def test1_a : Array Int := #[1, 2, 3]
def test1_b : Array Int := #[4, 5, 6]
def test1_Expected : Array Int := #[5, 7, 9]

-- Test case 2: empty arrays
def test2_a : Array Int := #[]
def test2_b : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: singleton arrays (includes 0)
def test3_a : Array Int := #[0]
def test3_b : Array Int := #[7]
def test3_Expected : Array Int := #[7]

-- Test case 4: singleton arrays with negative
def test4_a : Array Int := #[-3]
def test4_b : Array Int := #[10]
def test4_Expected : Array Int := #[7]

-- Test case 5: length 2 with mixed signs
def test5_a : Array Int := #[5, -2]
def test5_b : Array Int := #[-1, -8]
def test5_Expected : Array Int := #[4, -10]

-- Test case 6: all zeros
def test6_a : Array Int := #[0, 0, 0, 0]
def test6_b : Array Int := #[0, 0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 7: larger magnitude integers
def test7_a : Array Int := #[1000000, -1000000]
def test7_b : Array Int := #[2345678, 3456789]
def test7_Expected : Array Int := #[3345678, 2456789]

-- Test case 8: length 5 with alternating pattern
def test8_a : Array Int := #[1, -1, 1, -1, 1]
def test8_b : Array Int := #[-1, 1, -1, 1, -1]
def test8_Expected : Array Int := #[0, 0, 0, 0, 0]

-- Test case 9: length 1 boundary-like (both negative)
def test9_a : Array Int := #[-1]
def test9_b : Array Int := #[-1]
def test9_Expected : Array Int := #[-2]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
