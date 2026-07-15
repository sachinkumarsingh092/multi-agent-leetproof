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
    moveZeroes: Move all zero values in a list of integers to the end, preserving the relative order of non-zero elements.
    Natural language breakdown:
    1. Input is a list of integers xs, which may contain zeros and non-zeros.
    2. The output is a list of integers with the same length as xs.
    3. The output contains exactly the same multiset of integer values as xs (same multiplicities for every integer).
    4. All zeros in the output appear at the end (zeros form a suffix; equivalently, there is no non-zero element after a zero).
    5. The relative order of the non-zero elements is preserved from the input.
-/

section Specs
-- Helper: Bool predicate for “is non-zero” (for use with List.filter).
def isNonZeroB (x : Int) : Bool := x != 0

-- Helper: Bool predicate for “is zero” (for use with List.filter).
def isZeroB (x : Int) : Bool := x == 0

-- No input restrictions.
def precondition (xs : List Int) : Prop :=
  True

-- Property-based stable partition specification:
-- (a) length preserved
-- (b) all zeros are at the end (zeros form a suffix)
-- (c) multiset preserved via element counts
-- (d) order of non-zero elements preserved (as filtered subsequence equality)
def postcondition (xs : List Int) (result : List Int) : Prop :=
  result.length = xs.length ∧
  (∀ (i : Nat) (j : Nat), i < j → j < result.length → result[i]! = 0 → result[j]! = 0) ∧
  (∀ (x : Int), result.count x = xs.count x) ∧
  (result.filter isNonZeroB) = (xs.filter isNonZeroB)
end Specs

section Impl
method moveZeroes (xs : List Int)
  return (result : List Int)
  require precondition xs
  ensures postcondition xs result
  do
  pure ([])

prove_correct moveZeroes by sorry
end Impl

section TestCases
-- Test case 1: example from prompt
-- Example: [0, 1, 0, 3, 12] -> [1, 3, 12, 0, 0]
def test1_xs : List Int := [0, 1, 0, 3, 12]
def test1_Expected : List Int := [1, 3, 12, 0, 0]

-- Test case 2: empty list
def test2_xs : List Int := []
def test2_Expected : List Int := []

-- Test case 3: singleton zero
def test3_xs : List Int := [0]
def test3_Expected : List Int := [0]

-- Test case 4: singleton non-zero
def test4_xs : List Int := [7]
def test4_Expected : List Int := [7]

-- Test case 5: all zeros
def test5_xs : List Int := [0, 0, 0]
def test5_Expected : List Int := [0, 0, 0]

-- Test case 6: no zeros (includes a negative)
def test6_xs : List Int := [5, -1, 2]
def test6_Expected : List Int := [5, -1, 2]

-- Test case 7: zeros already at the end
def test7_xs : List Int := [1, 2, 3, 0, 0]
def test7_Expected : List Int := [1, 2, 3, 0, 0]

-- Test case 8: alternating zeros and non-zeros with negatives
def test8_xs : List Int := [0, -2, 0, -2, 0, 4]
def test8_Expected : List Int := [-2, -2, 4, 0, 0, 0]

-- Test case 9: a single zero in the middle
def test9_xs : List Int := [9, 8, 0, 7, 6]
def test9_Expected : List Int := [9, 8, 7, 6, 0]

-- Recommend to validate: length preservation, zero-suffix property, non-zero stability
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : List Int) :
  result ≠ test3_Expected →
  ¬ postcondition test3_xs result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
