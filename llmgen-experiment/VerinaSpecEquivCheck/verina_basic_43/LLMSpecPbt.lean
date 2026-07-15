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
    SumFourthPowersFirstNOdds: compute the sum of the fourth powers of the first n odd natural numbers.
    Natural language breakdown:
    1. The input n is a natural number representing how many odd numbers to include.
    2. The first n odd natural numbers are 1, 3, 5, ..., (2*n-1) (when n > 0).
    3. The required result is the sum of their fourth powers: ∑_{k=0}^{n-1} (2*k+1)^4.
    4. For n = 0, the sum is the empty sum, which equals 0.
    5. The result is a natural number.
    6. The intended result satisfies a closed-form identity (a theorem):
       15 * result = n * (2*n - 1) * (2*n + 1) * (12*n^2 - 7).
-/

section Specs
-- We use a closed-form characterization that uniquely determines the sum.
-- We avoid division in the postcondition by expressing the identity after multiplying by 15.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result * 15 = n * (2 * n - 1) * (2 * n + 1) * (12 * n * n - 7)
end Specs

section Impl
method SumFourthPowersFirstNOdds (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

prove_correct SumFourthPowersFirstNOdds by sorry
end Impl

section TestCases
-- Test case 1: n = 0 (empty sum)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 (1^4)
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 2 (1^4 + 3^4)
def test3_n : Nat := 2
def test3_Expected : Nat := 82

-- Test case 4: n = 3 (1^4 + 3^4 + 5^4)
def test4_n : Nat := 3
def test4_Expected : Nat := 707

-- Test case 5: n = 4 (add 7^4)
def test5_n : Nat := 4
def test5_Expected : Nat := 3108

-- Test case 6: n = 5 (add 9^4)
def test6_n : Nat := 5
def test6_Expected : Nat := 9669

-- Test case 7: n = 6 (add 11^4)
def test7_n : Nat := 6
def test7_Expected : Nat := 24310

-- Test case 8: n = 8 (skip to a larger input)
def test8_n : Nat := 8
def test8_Expected : Nat := 103496

-- Test case 9: n = 10 (larger input)
def test9_n : Nat := 10
def test9_Expected : Nat := 317338
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
