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
    ArmstrongNumber: determine whether a natural number `n` is an Armstrong (narcissistic) number.
    Natural language breakdown:
    1. Work in base 10 and consider the decimal digits of `n`.
    2. Let `k` be the number of decimal digits of `n`.
    3. Form the sum, over all decimal digits `d` of `n`, of `d^k`.
    4. `n` is an Armstrong number iff this digit-power sum equals `n`.
    5. The method returns `true` iff `n` is an Armstrong number; otherwise returns `false`.
    6. We use `Nat.digits 10 n` (Mathlib) for the digit decomposition (little-endian order).
-/

section Specs
-- Helper: decimal digits of `n` in base 10, little-endian (Mathlib `Nat.digits` convention).
-- Note: Mathlib defines `Nat.digits 10 0 = []`.
-- This still makes `0` Armstrong since the empty sum is `0`.
def decDigits (n : Nat) : List Nat :=
  Nat.digits 10 n

-- Helper: number of decimal digits according to `Nat.digits`.
def numDecDigits (n : Nat) : Nat :=
  (decDigits n).length

-- Helper: sum of digit^k, where k is the number of digits.
def armstrongSum (n : Nat) : Nat :=
  let k : Nat := numDecDigits n
  (decDigits n).foldl (fun (acc : Nat) (d : Nat) => acc + d ^ k) 0

-- Armstrong predicate in base 10.
def isArmstrong (n : Nat) : Prop :=
  armstrongSum n = n

-- No input restrictions.
def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ isArmstrong n)
end Specs

section Impl
method ArmstrongNumber (n : Nat)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure false  -- placeholder body only

end Impl

section TestCases
-- Test case 1: example Armstrong number 153
-- 153 = 1^3 + 5^3 + 3^3

def test1_n : Nat := 153
def test1_Expected : Bool := true

-- Test case 2: boundary n = 0 (Mathlib digits=[], sum=0)

def test2_n : Nat := 0
def test2_Expected : Bool := true

-- Test case 3: boundary n = 1 (single digit)

def test3_n : Nat := 1
def test3_Expected : Bool := true

-- Test case 4: single digit 9 (single digit)

def test4_n : Nat := 9
def test4_Expected : Bool := true

-- Test case 5: first two-digit number

def test5_n : Nat := 10
def test5_Expected : Bool := false

-- Test case 6: close to an Armstrong example but not Armstrong

def test6_n : Nat := 154
def test6_Expected : Bool := false

-- Test case 7: Armstrong number 370

def test7_n : Nat := 370
def test7_Expected : Bool := true

-- Test case 8: Armstrong number 371

def test8_n : Nat := 371
def test8_Expected : Bool := true

-- Test case 9: larger non-Armstrong near a known 4-digit Armstrong

def test9_n : Nat := 9475
def test9_Expected : Bool := false

-- Recommend to validate: 0, 1, 153
end TestCases
