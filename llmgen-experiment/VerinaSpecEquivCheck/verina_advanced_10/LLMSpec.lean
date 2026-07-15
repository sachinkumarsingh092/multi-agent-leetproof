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
    PrimeFactorExponents: decompose a positive natural number into exponents of user-provided primes
    Natural language breakdown:
    1. Inputs are a natural number n and a non-empty list primes.
    2. n is positive (n > 0).
    3. primes contains distinct prime numbers.
    4. Every prime divisor of n must be contained in primes (so primes covers all prime factors of n).
    5. The output is a list of pairs (p, e) where p is a prime from the input list and e is a natural number.
    6. The output list has the same length as primes, and preserves the order of primes (pair i corresponds to primes[i]).
    7. For each output pair (p,e), p^e divides n, but p^(e+1) does not divide n; this characterizes e as the exponent of p in the prime factorization of n.
    8. Every prime in primes must appear exactly once as the first component of some pair in the output (guaranteed by order-preserving alignment).
-/

section Specs
-- Helper: multiply all prime powers described by a list of pairs.
-- (p,e) contributes p^e.
def primePowerProduct (l : List (Nat × Nat)) : Nat :=
  (l.map (fun pe : Nat × Nat => pe.1 ^ pe.2)).prod

-- Helper: semantic characterization of the exponent of p in n.
-- e is the unique exponent such that p^e ∣ n but p^(e+1) ∤ n.
def isPrimeExponentOf (n : Nat) (p : Nat) (e : Nat) : Prop :=
  (p ^ e ∣ n) ∧ ¬ (p ^ (e + 1) ∣ n)

def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes ≠ [] ∧
  primes.Nodup ∧
  (∀ p : Nat, p ∈ primes → Nat.Prime p) ∧
  -- Coverage: if a prime divides n, it must be listed.
  (∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ primes)

def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) : Prop :=
  -- One output pair per input prime, and positional alignment to make the result unique.
  result.length = primes.length ∧
  (∀ i : Nat, i < primes.length →
    let p := primes.get! i
    let pe := result.get! i
    pe.1 = p ∧
    Nat.Prime p ∧
    isPrimeExponentOf n p pe.2) ∧
  -- Reconstruction: multiplying all returned prime powers yields n.
  n = primePowerProduct result
end Specs

section Impl
method PrimeFactorExponents (n : Nat) (primes : List Nat)
  return (result : List (Nat × Nat))
  require precondition n primes
  ensures postcondition n primes result
  do
  pure []

end Impl

section TestCases
-- Test case 1: typical factorization, n = 60 = 2^2 * 3^1 * 5^1
-- (Example provided in previous attempts; keep as test 1.)
def test1_n : Nat := 60
def test1_primes : List Nat := [2, 3, 5]
def test1_Expected : List (Nat × Nat) := [(2, 2), (3, 1), (5, 1)]

-- Test case 2: boundary valid n = 1, exponent is 0 for any listed prime
def test2_n : Nat := 1
def test2_primes : List Nat := [2]
def test2_Expected : List (Nat × Nat) := [(2, 0)]

-- Test case 3: smallest prime power
def test3_n : Nat := 2
def test3_primes : List Nat := [2]
def test3_Expected : List (Nat × Nat) := [(2, 1)]

-- Test case 4: multiple primes with higher exponents, n = 72 = 2^3 * 3^2
def test4_n : Nat := 72
def test4_primes : List Nat := [2, 3]
def test4_Expected : List (Nat × Nat) := [(2, 3), (3, 2)]

-- Test case 5: primes list includes a prime not dividing n, exponent should be 0
def test5_n : Nat := 12
def test5_primes : List Nat := [2, 3, 5]
def test5_Expected : List (Nat × Nat) := [(2, 2), (3, 1), (5, 0)]

-- Test case 6: n itself is prime
def test6_n : Nat := 13
def test6_primes : List Nat := [13]
def test6_Expected : List (Nat × Nat) := [(13, 1)]

-- Test case 7: order is preserved; primes in a different order yield correspondingly ordered result
-- n = 60 = 2^2 * 3^1 * 5^1
-- primes = [5,2,3] implies result = [(5,1),(2,2),(3,1)]
def test7_n : Nat := 60
def test7_primes : List Nat := [5, 2, 3]
def test7_Expected : List (Nat × Nat) := [(5, 1), (2, 2), (3, 1)]

-- Test case 8: large exponent, n = 2^10
def test8_n : Nat := 1024
def test8_primes : List Nat := [2]
def test8_Expected : List (Nat × Nat) := [(2, 10)]

-- Test case 9: another composite with an extra unused prime
-- n = 36 = 2^2 * 3^2, include 5 with exponent 0
def test9_n : Nat := 36
def test9_primes : List Nat := [2, 3, 5]
def test9_Expected : List (Nat × Nat) := [(2, 2), (3, 2), (5, 0)]

-- Recommend to validate: n=99991 with primes=[99991], n=36 with primes=[2,3,5], n=1 with primes=[2,3,5]
end TestCases
