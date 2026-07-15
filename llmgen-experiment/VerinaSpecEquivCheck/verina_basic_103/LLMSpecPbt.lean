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
    verina_basic_103: update an integer array at two fixed 0-based indices
    Natural language breakdown:
    1. Input is an array of integers `a`.
    2. The array is assumed to contain at least 8 elements (so indices 4 and 7 are valid).
    3. The output is an array `result` with the same size as `a`.
    4. At index 4, the output element equals the original element at index 4 plus 3.
    5. At index 7, the output element equals 516.
    6. At every other index, the output element equals the input element at that index.
    7. Indices are 0-indexed.
-/

section Specs
-- No custom helpers are required; we specify the update pointwise by index.

def precondition (a : Array Int) : Prop :=
  a.size ≥ 8

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < a.size →
    ((i = 4 → result[i]! = a[i]! + 3) ∧
     (i = 7 → result[i]! = 516) ∧
     (i ≠ 4 ∧ i ≠ 7 → result[i]! = a[i]!)))
end Specs

section Impl
method UpdateArray103 (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  -- Placeholder implementation only
  pure a

prove_correct UpdateArray103 by sorry
end Impl

section TestCases
-- Test case 1: boundary size = 8
def test1_a : Array Int := #[0, 1, 2, 3, 4, 5, 6, 7]
def test1_Expected : Array Int := #[0, 1, 2, 3, 7, 5, 6, 516]

-- Test case 2: size > 8, other elements unchanged
def test2_a : Array Int := #[10, 20, 30, 40, 50, 60, 70, 80, 90]
def test2_Expected : Array Int := #[10, 20, 30, 40, 53, 60, 70, 516, 90]

-- Test case 3: negative values present, include -1
def test3_a : Array Int := #[-1, -2, -3, -4, -5, -6, -7, -8]
def test3_Expected : Array Int := #[-1, -2, -3, -4, -2, -6, -7, 516]

-- Test case 4: index 4 and 7 already special values
def test4_a : Array Int := #[99, 0, 0, 0, 513, 1, 2, 516]
def test4_Expected : Array Int := #[99, 0, 0, 0, 516, 1, 2, 516]

-- Test case 5: zeros everywhere
def test5_a : Array Int := #[0, 0, 0, 0, 0, 0, 0, 0]
def test5_Expected : Array Int := #[0, 0, 0, 0, 3, 0, 0, 516]

-- Test case 6: mixed signs, ensure only positions 4 and 7 change
def test6_a : Array Int := #[1, -1, 2, -2, 3, -3, 4, -4, 5, -5]
def test6_Expected : Array Int := #[1, -1, 2, -2, 6, -3, 4, 516, 5, -5]

-- Test case 7: large magnitude values
def test7_a : Array Int := #[1000000, 2000000, 3000000, 4000000, -1000000, 6, 7, 8]
def test7_Expected : Array Int := #[1000000, 2000000, 3000000, 4000000, -999997, 6, 7, 516]

-- Test case 8: repeated values, check stability of other indices
def test8_a : Array Int := #[42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
def test8_Expected : Array Int := #[42, 42, 42, 42, 45, 42, 42, 516, 42, 42, 42]
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
