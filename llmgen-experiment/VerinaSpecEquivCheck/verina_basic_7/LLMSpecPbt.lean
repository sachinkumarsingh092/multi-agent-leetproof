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
    SumSquaresFirstNOdds: compute the sum of the squares of the first n odd natural numbers.

    Natural language breakdown:
    1. The input n is a natural number denoting how many initial odd numbers to include.
    2. The odd numbers considered are 1, 3, 5, ..., (2*n-1).
    3. The required output is the sum of their squares: 1^2 + 3^2 + ... + (2*n-1)^2.
    4. This sum is characterized by the closed-form identity:
       sum = (n * (2*n - 1) * (2*n + 1)) / 3.
    5. Since the right-hand side uses Nat division, the specification must ensure the result is the
       unique natural number whose multiplication by 3 equals n * (2*n - 1) * (2*n + 1).
-/

section Specs
-- Helper: the numerator polynomial appearing in the closed-form.
-- Note: Nat subtraction is truncated, but for n = 0 we still get numerator = 0.
def oddSquaresNumerator (n : Nat) : Nat :=
  n * (2 * n - 1) * (2 * n + 1)

-- No input restrictions: n is already non-negative by type.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: result is the unique Nat such that result*3 equals the numerator.
-- This avoids relying on truncating Nat division in the specification.
def postcondition (n : Nat) (result : Nat) : Prop :=
  result * 3 = oddSquaresNumerator n
end Specs

section Impl
method SumSquaresFirstNOdds (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    pure 0

prove_correct SumSquaresFirstNOdds by sorry
end Impl

section TestCases
-- Test case 1: n = 0 (empty sum)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 (1^2 = 1)
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2 (1^2 + 3^2 = 10)
def test3_n : Nat := 2
def test3_Expected : Nat := 10

-- Test case 4: n = 3 (1^2 + 3^2 + 5^2 = 35)
def test4_n : Nat := 3
def test4_Expected : Nat := 35

-- Test case 5: n = 4 (1^2 + 3^2 + 5^2 + 7^2 = 84)
def test5_n : Nat := 4
def test5_Expected : Nat := 84

-- Test case 6: n = 5 (previous + 9^2 = 165)
def test6_n : Nat := 5
def test6_Expected : Nat := 165

-- Test case 7: n = 10 (larger typical input)
def test7_n : Nat := 10
def test7_Expected : Nat := 1330

-- Test case 8: n = 50 (stress a larger number while staying within Nat)
def test8_n : Nat := 50
def test8_Expected : Nat := 166650
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Nat) :
  result ≠ test8_Expected →
  ¬ postcondition test8_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
