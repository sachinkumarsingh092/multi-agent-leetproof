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
    BinaryDigitsToNat: Convert a binary number represented as a list of digits (big-endian) to a natural number.
    Natural language breakdown:
    1. The input is a list of natural-number digits in big-endian order (most significant digit first).
    2. Each digit must be either 0 or 1.
    3. The output is the natural number whose base-2 bit pattern matches the input digits.
    4. The least significant bit of the result corresponds to the last digit of the list.
    5. Bits at positions beyond the length of the input list are false (so the result is < 2^(length)).
    6. The empty list represents the number 0.
-/

section Specs
-- Helper: digit validity predicate
def isBitDigit (d : Nat) : Prop := d = 0 ∨ d = 1

-- Helper: interpret a digit as a Bool bit (true iff digit is 1)
def digitToBit (d : Nat) : Bool := (d == 1)

-- Helper: kth digit from the right (least significant side), using total indexing.
-- This is intended to be used only under the guard k < digits.length.
def digitFromRight (digits : List Nat) (k : Nat) : Nat :=
  digits.get! (digits.length - 1 - k)

def precondition (digits : List Nat) : Prop :=
  ∀ (d : Nat), d ∈ digits → isBitDigit d

def postcondition (digits : List Nat) (result : Nat) : Prop :=
  (∀ (k : Nat), k < digits.length → result.testBit k = digitToBit (digitFromRight digits k)) ∧
  (∀ (k : Nat), digits.length ≤ k → result.testBit k = false)
end Specs

section Impl
method BinaryDigitsToNat (digits : List Nat)
  return (result : Nat)
  require precondition digits
  ensures postcondition digits result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: typical binary number 100₂ = 4
def test1_digits : List Nat := [1, 0, 0]
def test1_Expected : Nat := 4

-- Test case 2: empty list represents 0
def test2_digits : List Nat := []
def test2_Expected : Nat := 0

-- Test case 3: single digit 0
def test3_digits : List Nat := [0]
def test3_Expected : Nat := 0

-- Test case 4: single digit 1
def test4_digits : List Nat := [1]
def test4_Expected : Nat := 1

-- Test case 5: leading zeros allowed, 001₂ = 1
def test5_digits : List Nat := [0, 0, 1]
def test5_Expected : Nat := 1

-- Test case 6: 1011₂ = 11
def test6_digits : List Nat := [1, 0, 1, 1]
def test6_Expected : Nat := 11

-- Test case 7: all zeros
def test7_digits : List Nat := [0, 0, 0, 0]
def test7_Expected : Nat := 0

-- Test case 8: 11111₂ = 31
def test8_digits : List Nat := [1, 1, 1, 1, 1]
def test8_Expected : Nat := 31

-- Test case 9: alternating bits, 010101₂ = 21
def test9_digits : List Nat := [0, 1, 0, 1, 0, 1]
def test9_Expected : Nat := 21
end TestCases
