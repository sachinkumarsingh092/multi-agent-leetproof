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
    IsPrime: decide whether a given natural number n is prime.

    Natural language breakdown:
    1. Input is a natural number n.
    2. The input is expected to satisfy n ≥ 2.
    3. A natural number n is prime exactly when its only positive divisors are 1 and n.
    4. Equivalently: n is prime iff there is no k with 1 < k < n such that k ∣ n.
    5. The method returns a Boolean indicating whether n is prime.
-/

section Specs
-- We use Mathlib's canonical primality predicate on Nat.

def precondition (n : Nat) : Prop :=
  n ≥ 2

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ Nat.Prime n)
end Specs

section Impl
method IsPrime (n : Nat)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  -- Placeholder body only (specification-focused task)
  pure true

end Impl

section TestCases
-- Test case 1: boundary prime (smallest valid input)
def test1_n : Nat := 2
def test1_Expected : Bool := true

-- Test case 2: small prime
def test2_n : Nat := 3
def test2_Expected : Bool := true

-- Test case 3: small composite (even)
def test3_n : Nat := 4
def test3_Expected : Bool := false

-- Test case 4: another small prime
def test4_n : Nat := 5
def test4_Expected : Bool := true

-- Test case 5: composite (product of two primes)
def test5_n : Nat := 6

def test5_Expected : Bool := false

-- Test case 6: perfect square composite
def test6_n : Nat := 9
def test6_Expected : Bool := false

-- Test case 7: odd composite not a square
def test7_n : Nat := 15
def test7_Expected : Bool := false

-- Test case 8: larger prime
def test8_n : Nat := 97
def test8_Expected : Bool := true

-- Test case 9: larger composite (power of 2)
def test9_n : Nat := 1024
def test9_Expected : Bool := false
end TestCases
