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
    LastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. The input is a natural number n (non-negative integer).
    2. The output is a natural number result representing the last decimal digit of n.
    3. The last digit is the remainder when dividing n by 10.
    4. The result must always be a valid decimal digit, i.e., it lies between 0 and 9.
-/

section Specs
-- Helper definition: being a decimal digit (0..9) for natural numbers.
def IsDecimalDigit (d : Nat) : Prop := d < 10

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = n % 10 ∧ IsDecimalDigit result
end Specs

section Impl
method LastDigit (n : Nat) return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
    pure 0

end Impl

section TestCases
-- Test case 1: n = 0 (boundary)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: n = 1 (boundary)
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: n = 9 (largest single digit)
def test3_n : Nat := 9
def test3_Expected : Nat := 9

-- Test case 4: n = 10 (multiple of 10)
def test4_n : Nat := 10
def test4_Expected : Nat := 0

-- Test case 5: n = 11 (two-digit, last digit 1)
def test5_n : Nat := 11
def test5_Expected : Nat := 1

-- Test case 6: n = 19 (two-digit, last digit 9)
def test6_n : Nat := 19
def test6_Expected : Nat := 9

-- Test case 7: n = 20 (multiple of 10 > 10)
def test7_n : Nat := 20
def test7_Expected : Nat := 0

-- Test case 8: n = 12345 (typical large number)
def test8_n : Nat := 12345
def test8_Expected : Nat := 5

-- Test case 9: n = 999999 (many digits, last digit 9)
def test9_n : Nat := 999999
def test9_Expected : Nat := 9
end TestCases
