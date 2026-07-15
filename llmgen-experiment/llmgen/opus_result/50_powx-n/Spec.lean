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
    Pow(x, n, p): compute x raised to the power n modulo p.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. Inputs are an integer base x, a natural-number exponent n, and an integer modulus p.
    2. The modulus must be positive (p > 0) so that the modulo operation has a standard range of remainders.
    3. The output is the remainder of x^n upon division by p.
    4. The output must be the unique integer r such that 0 ≤ r < p and r ≡ x^n (mod p).
    5. Edge cases include n = 0 (so x^0 = 1), x = 0, negative x, and p = 1 (so the only remainder is 0).
-/

section Specs
-- The standard modular exponentiation result is characterized by:
-- (i) range constraints 0 ≤ result < p, and
-- (ii) congruence result ≡ x^n [ZMOD p].
-- These jointly make the result unique.

def precondition (x : Int) (n : Nat) (p : Int) : Prop :=
  p > 0

def postcondition (x : Int) (n : Nat) (p : Int) (result : Int) : Prop :=
  0 ≤ result ∧ result < p ∧ Int.ModEq p result (x ^ n)
end Specs

section Impl
method PowMod (x : Int) (n : Nat) (p : Int)
  return (result : Int)
  require precondition x n p
  ensures postcondition x n p result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1
-- x = 2, n = 10, p = 1000 => 24
-- 2^10 = 1024, 1024 mod 1000 = 24

def test1_x : Int := 2
def test1_n : Nat := 10
def test1_p : Int := 1000
def test1_Expected : Int := 24

-- Test case 2: Example 2

def test2_x : Int := 3
def test2_n : Nat := 5
def test2_p : Int := 13
def test2_Expected : Int := 9

-- Test case 3: Example 3

def test3_x : Int := 7
def test3_n : Nat := 1
def test3_p : Int := 7
def test3_Expected : Int := 0

-- Test case 4: Edge case n = 0 (x^0 = 1)

def test4_x : Int := 5
def test4_n : Nat := 0
def test4_p : Int := 7
def test4_Expected : Int := 1

-- Test case 5: Edge case p = 1 (only remainder is 0)

def test5_x : Int := 123
def test5_n : Nat := 456
def test5_p : Int := 1
def test5_Expected : Int := 0

-- Test case 6: Edge case x = 0 and n > 0

def test6_x : Int := 0
def test6_n : Nat := 5
def test6_p : Int := 17
def test6_Expected : Int := 0

-- Test case 7: Negative base
-- (-2)^3 = -8, (-8) mod 5 = 2

def test7_x : Int := -2
def test7_n : Nat := 3
def test7_p : Int := 5
def test7_Expected : Int := 2

-- Test case 8: Larger exponent
-- 2^100 mod 13 = 3

def test8_x : Int := 2
def test8_n : Nat := 100
def test8_p : Int := 13
def test8_Expected : Int := 3

-- Test case 9: Small modulus

def test9_x : Int := 10
def test9_n : Nat := 1
def test9_p : Int := 3
def test9_Expected : Int := 1

-- Test case 10: Base 1

def test10_x : Int := 1
def test10_n : Nat := 999
def test10_p : Int := 2
def test10_Expected : Int := 1
end TestCases
