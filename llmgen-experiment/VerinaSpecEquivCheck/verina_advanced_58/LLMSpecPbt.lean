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
    NthUglyNumber: return the n-th ugly number (1-based), where ugly numbers are positive integers
    whose only prime factors are 2, 3, or 5.

    Natural language breakdown:
    1. The input n is a 1-based index; n = 1 asks for the first ugly number.
    2. An ugly number is a positive natural number.
    3. A positive natural number x is ugly iff every prime p that divides x is one of 2, 3, or 5.
    4. Ugly numbers are ordered by the usual ≤ on Nat.
    5. The function returns the unique ugly number result such that:
       a. Exactly n ugly numbers are ≤ result.
       b. Exactly n-1 ugly numbers are ≤ (result - 1).
-/

section Specs
-- An ugly number is positive and has no prime divisors other than 2, 3, or 5.
-- This is purely relational (no factorization API required).
def IsUgly (x : Nat) : Prop :=
  x > 0 ∧
  ∀ (p : Nat), Nat.Prime p → p ∣ x → (p = 2 ∨ p = 3 ∨ p = 5)

-- Count ugly numbers in the bounded range [0, r].
-- We use Classical decidability to be able to filter by the Prop predicate `IsUgly`.
noncomputable def countUglyUpTo (r : Nat) : Nat :=
  by
    classical
    exact ((Finset.range (r + 1)).filter IsUgly).card

-- Input is a 1-based index into the increasing sequence of ugly numbers.
def precondition (n : Nat) : Prop :=
  n ≥ 1

-- Postcondition: result is the n-th ugly number.
-- Characterization via counting within a bounded range ensures the set is finite in Lean.
-- The pair of equalities pins down the unique n-th ugly number:
-- - there are exactly n ugly numbers ≤ result
-- - there are exactly n-1 ugly numbers ≤ result-1 (so result is the next ugly number)
def postcondition (n : Nat) (result : Nat) : Prop :=
  IsUgly result ∧
  countUglyUpTo result = n ∧
  countUglyUpTo (result - 1) = (n - 1)
end Specs

section Impl
method NthUglyNumber (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  -- Placeholder implementation only
  pure 1

prove_correct NthUglyNumber by sorry
end Impl

section TestCases
-- Test case 1: base case (given statement: first ugly number is 1)
def test1_n : Nat := 1
def test1_Expected : Nat := 1

-- Test case 2: n = 2
-- Ugly numbers start: 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, ...
def test2_n : Nat := 2
def test2_Expected : Nat := 2

-- Test case 3: n = 3
def test3_n : Nat := 3
def test3_Expected : Nat := 3

-- Test case 4: n = 7 (skips 7; next is 8)
def test4_n : Nat := 7
def test4_Expected : Nat := 8

-- Test case 5: n = 10
def test5_n : Nat := 10
def test5_Expected : Nat := 12

-- Test case 6: n = 11
def test6_n : Nat := 11
def test6_Expected : Nat := 15

-- Test case 7: n = 15
def test7_n : Nat := 15
def test7_Expected : Nat := 24

-- Test case 8: n = 20
def test8_n : Nat := 20
def test8_Expected : Nat := 36

-- Test case 9: n = 50
def test9_n : Nat := 50
def test9_Expected : Nat := 243

-- Recommend to validate: test1_n, test7_n, test9_n
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
