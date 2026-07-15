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
    AddTwoNumbers (reversed digit lists): Add two non-empty linked lists representing non-negative integers.

    Natural language breakdown:
    1. Each input is a non-empty list of decimal digits, stored in reverse order (head is least significant digit).
    2. Each digit is a natural number between 0 and 9 (inclusive).
    3. Each input list represents a non-negative integer using base-10 positional value.
    4. The output is a non-empty list of decimal digits in the same reverse order.
    5. The numeric value represented by the output equals the sum of the numeric values represented by the inputs.
    6. The output is a canonical digit list: it contains no unnecessary most-significant zeros.
       Concretely, if the represented value is 0 then the result is exactly [0]; otherwise the last digit is nonzero.
-/

section Specs
-- A digit list is valid (base 10) iff all elements are < 10.
-- We use strict inequality (< 10) because digits are naturals.
def allDigitsBase10 (l : List Nat) : Prop :=
  ∀ (d : Nat), d ∈ l → d < 10

-- The base-10 value of a little-endian (reversed) digit list.
-- Mathlib's Nat.ofDigits uses the little-endian convention.
def valueBase10LE (l : List Nat) : Nat :=
  Nat.ofDigits 10 l

-- Canonicality for a base-10 little-endian digit list:
-- it is non-empty, all digits are valid, and it has no unnecessary most-significant zeros.
-- We treat 0 specially: the unique canonical representation is [0].
def canonicalBase10LE (l : List Nat) : Prop :=
  l ≠ [] ∧
  allDigitsBase10 l ∧
  ((valueBase10LE l = 0) ↔ (l = [0])) ∧
  (valueBase10LE l ≠ 0 → l.getLast? ≠ some 0)

-- Inputs are required to be non-empty and contain only decimal digits.
-- (We do not require canonical inputs; leading zeros are allowed in the most-significant positions.)
def precondition (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1 ≠ [] ∧
  l2 ≠ [] ∧
  allDigitsBase10 l1 ∧
  allDigitsBase10 l2

-- The output must be a canonical base-10 little-endian digit list representing the sum.
def postcondition (l1 : List Nat) (l2 : List Nat) (result : List Nat) : Prop :=
  canonicalBase10LE result ∧
  valueBase10LE result = valueBase10LE l1 + valueBase10LE l2
end Specs

section Impl
method AddTwoNumbers (l1 : List Nat) (l2 : List Nat)
  return (result : List Nat)
  require precondition l1 l2
  ensures postcondition l1 l2 result
  do
  pure [0]  -- placeholder body only

end Impl

section TestCases
-- Test case 1: typical multi-digit addition with carry propagation (LeetCode-style)
-- 342 + 465 = 807
-- l1 = [2,4,3], l2 = [5,6,4] => [7,0,8]
def test1_l1 : List Nat := [2, 4, 3]
def test1_l2 : List Nat := [5, 6, 4]
def test1_Expected : List Nat := [7, 0, 8]

-- Test case 2: smallest digits, zero + zero
-- 0 + 0 = 0

def test2_l1 : List Nat := [0]
def test2_l2 : List Nat := [0]
def test2_Expected : List Nat := [0]

-- Test case 3: single-digit with carry
-- 9 + 1 = 10

def test3_l1 : List Nat := [9]
def test3_l2 : List Nat := [1]
def test3_Expected : List Nat := [0, 1]

-- Test case 4: different lengths
-- 1 + 999 = 1000

def test4_l1 : List Nat := [1]
def test4_l2 : List Nat := [9, 9, 9]
def test4_Expected : List Nat := [0, 0, 0, 1]

-- Test case 5: inputs with extra most-significant zeros (allowed), output should be canonical
-- [1,0,0] represents 1; 1 + 0 = 1

def test5_l1 : List Nat := [1, 0, 0]
def test5_l2 : List Nat := [0]
def test5_Expected : List Nat := [1]

-- Test case 6: long carry chain
-- 9999 + 9999 = 19998

def test6_l1 : List Nat := [9, 9, 9, 9]
def test6_l2 : List Nat := [9, 9, 9, 9]
def test6_Expected : List Nat := [8, 9, 9, 9, 1]

-- Test case 7: adding zero to a number
-- 321 + 0 = 321

def test7_l1 : List Nat := [1, 2, 3]
def test7_l2 : List Nat := [0]
def test7_Expected : List Nat := [1, 2, 3]

-- Test case 8: both have leading zeros and sum is zero; output must be [0]
-- [0,0,0] and [0,0] both represent 0

def test8_l1 : List Nat := [0, 0, 0]
def test8_l2 : List Nat := [0, 0]
def test8_Expected : List Nat := [0]

-- Test case 9: mixed carries across uneven lengths
-- 95 + 7 = 102

def test9_l1 : List Nat := [5, 9]
def test9_l2 : List Nat := [7]
def test9_Expected : List Nat := [2, 0, 1]
end TestCases
