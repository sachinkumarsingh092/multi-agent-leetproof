import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    DivBy8OrHasDigit8: decide whether an integer is divisible by 8 or has decimal digit 8.
    Natural language breakdown:
    1. The input is an integer n (it may be negative, zero, or positive).
    2. The output is a boolean.
    3. The output should be true exactly when either condition holds:
       a) n is divisible by 8 (remainder of Euclidean division by 8 is 0), or
       b) the base-10 (decimal) representation of |n| contains the digit 8.
    4. For digit checking, the sign of n is ignored; only the digits of the absolute value matter.
    5. The digit condition is existential: at least one digit equals 8.
-/

section Specs
-- Helper predicate: |n| has a decimal digit equal to 8.
-- We use Nat.digits 10 on the absolute value (as a Nat) to get base-10 digits.

def hasDigit8 (n : Int) : Prop :=
  (8 : Nat) ∈ Nat.digits 10 n.natAbs

-- Helper predicate: n is divisible by 8.
-- Int's `%` is Euclidean remainder (Int.emod), so this works uniformly for negative integers.

def divisibleBy8 (n : Int) : Prop :=
  n % (8 : Int) = 0

-- No input restrictions.

def precondition (n : Int) : Prop :=
  True

-- Postcondition: result is true iff n is divisible by 8 or has an 8 digit.
-- We avoid `decide` to not require a `Decidable` instance for the proposition.

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ (divisibleBy8 n ∨ hasDigit8 n))
end Specs

section Impl
method DivBy8OrHasDigit8 (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
    pure false

prove_correct DivBy8OrHasDigit8 by sorry
end Impl

section TestCases
-- Test case 1: n = 0 (edge case; divisible by 8)
def test1_n : Int := 0
def test1_Expected : Bool := true

-- Test case 2: n = 1 (edge case; not divisible by 8 and no digit 8)
def test2_n : Int := 1
def test2_Expected : Bool := false

-- Test case 3: n = -1 (edge case negative; not divisible by 8 and no digit 8)
def test3_n : Int := -1
def test3_Expected : Bool := false

-- Test case 4: n = 16 (divisible by 8)
def test4_n : Int := 16
def test4_Expected : Bool := true

-- Test case 5: n = -24 (negative divisible by 8)
def test5_n : Int := -24
def test5_Expected : Bool := true

-- Test case 6: n = 18 (contains digit 8, not divisible by 8)
def test6_n : Int := 18
def test6_Expected : Bool := true

-- Test case 7: n = -81 (contains digit 8, negative)
def test7_n : Int := -81
def test7_Expected : Bool := true

-- Test case 8: n = 7 (neither divisible by 8 nor contains digit 8)
def test8_n : Int := 7
def test8_Expected : Bool := false

-- Test case 9: n = 88 (contains digit 8 and is divisible by 8)
def test9_n : Int := 88
def test9_Expected : Bool := true

-- Recommend to validate: 0, 1, -1
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1' (result : Bool) :
  result ≠ test1_Expected →
  ¬ postcondition test1_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
