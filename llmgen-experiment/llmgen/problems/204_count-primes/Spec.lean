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
    204. Count Primes: given a non-negative integer n, return the number of prime numbers strictly less than n.
    **Important: complexity should be O(n log log n) time and O(n) space**
    Natural language breakdown:
    1. The input n is a natural number representing an exclusive upper bound.
    2. A number p is counted iff p is a natural prime (Nat.Prime p) and p < n.
    3. The output is the count of such primes; equivalently, the cardinality of the finite set of primes in {0,1,...,n-1}.
    4. For n ≤ 2, the count is 0 because there are no primes < 2.
    5. The specification characterizes the result purely by set cardinality (no algorithm mandated).
-/

section Specs
-- Helper: the finite set of primes strictly less than n.
-- Using Mathlib's Nat.Prime and Finset.range.
def primeSetBelow (n : Nat) : Finset Nat :=
  (Finset.range n).filter Nat.Prime

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (primeSetBelow n).card ∧
  result ≤ n
end Specs

section Impl
method CountPrimes (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: example n = 10
-- Primes < 10 are 2,3,5,7 => 4

def test1_n : Nat := 10
def test1_Expected : Nat := 4

-- Test case 2: example n = 0

def test2_n : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: example n = 1

def test3_n : Nat := 1
def test3_Expected : Nat := 0

-- Test case 4: boundary n = 2

def test4_n : Nat := 2
def test4_Expected : Nat := 0

-- Test case 5: small n = 3, primes < 3 is {2}

def test5_n : Nat := 3
def test5_Expected : Nat := 1

-- Test case 6: small n = 4, primes < 4 are 2,3

def test6_n : Nat := 4
def test6_Expected : Nat := 2

-- Test case 7: small n = 5, primes < 5 are 2,3

def test7_n : Nat := 5
def test7_Expected : Nat := 2

-- Test case 8: moderate n = 20, primes < 20 are 2,3,5,7,11,13,17,19

def test8_n : Nat := 20
def test8_Expected : Nat := 8

-- Test case 9: larger n = 100, known count is 25

def test9_n : Nat := 100
def test9_Expected : Nat := 25
end TestCases
