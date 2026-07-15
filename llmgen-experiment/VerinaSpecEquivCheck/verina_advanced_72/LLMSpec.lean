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
    verina_advanced_72: smallest prime factor less than 10
    Natural language breakdown:
    1. Input is a natural number n.
    2. A number p is a prime factor of n if Nat.Prime p and p ∣ n.
    3. We only consider prime factors p with p < 10.
    4. If there exists at least one such prime factor, the result is the smallest one.
    5. If no prime factor of n is less than 10, the result is 0.
    6. The output is a natural number.
-/

section Specs
-- A candidate “small prime factor” is a prime divisor below 10.
def IsSmallPrimeFactor (n : Nat) (p : Nat) : Prop :=
  Nat.Prime p ∧ p ∣ n ∧ p < 10

-- No preconditions: defined for all natural numbers n.
def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  -- Either there is no small prime factor and we return 0,
  -- or result is the smallest small prime factor.
  (result = 0 ∧ (∀ (p : Nat), IsSmallPrimeFactor n p → False)) ∨
  (IsSmallPrimeFactor n result ∧ (∀ (p : Nat), IsSmallPrimeFactor n p → result ≤ p))
end Specs

section Impl
method SmallestPrimeFactorLt10 (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical composite with small prime factors (15 = 3 * 5)
def test1_n : Nat := 15
def test1_Expected : Nat := 3

-- Test case 2: boundary n = 0 (all positive numbers divide 0, smallest prime < 10 is 2)
def test2_n : Nat := 0
def test2_Expected : Nat := 2

-- Test case 3: boundary n = 1 has no prime factors
def test3_n : Nat := 1
def test3_Expected : Nat := 0

-- Test case 4: n itself is a small prime
def test4_n : Nat := 2
def test4_Expected : Nat := 2

-- Test case 5: prime factor is 3 (9 = 3^2)
def test5_n : Nat := 9
def test5_Expected : Nat := 3

-- Test case 6: only small prime factor is 5 (25 = 5^2)
def test6_n : Nat := 25
def test6_Expected : Nat := 5

-- Test case 7: only small prime factor is 7 (49 = 7^2)
def test7_n : Nat := 49
def test7_Expected : Nat := 7

-- Test case 8: no prime factor < 10 (121 = 11^2)
def test8_n : Nat := 121
def test8_Expected : Nat := 0

-- Test case 9: n is a prime greater than 10
def test9_n : Nat := 11
def test9_Expected : Nat := 0

-- Test case 10: multiple small prime factors, smallest is 2 (210 = 2 * 3 * 5 * 7)
def test10_n : Nat := 210
def test10_Expected : Nat := 2
end TestCases
