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
    verina_basic_18: Compute the sum of the decimal digits of a non-negative integer.

    Natural language breakdown:
    1. The input n is a natural number (non-negative integer).
    2. Interpret n in base 10, i.e., as a sequence of decimal digits.
    3. The output result is the sum of all those decimal digits.
    4. The output is a natural number.
    5. Edge cases:
       - If n = 0, the digit sequence is [0], so the sum is 0.
       - Powers of 10 have digit sum 1.

    Notes on specification style:
    - We use Mathlib's canonical digit decomposition `Nat.digits 10 n : List Nat`.
    - The required digit sum is the sum of that list.
-/

section Specs
-- `Nat.digits 10 n` is the canonical list of base-10 digits of `n` in little-endian order.
-- The required result is the sum of those digits.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = (Nat.digits 10 n).sum
end Specs

section Impl
method SumDigits (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0  -- placeholder

prove_correct SumDigits by sorry
end Impl

section TestCases
-- Test case 1: n = 0 (degenerate case)
def test1_n : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: single digit 1
def test2_n : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: single digit 9
def test3_n : Nat := 9
def test3_Expected : Nat := 9

-- Test case 4: boundary crossing 10 -> digits [1,0]
def test4_n : Nat := 10
def test4_Expected : Nat := 1

-- Test case 5: small two-digit number 11 -> 1+1
def test5_n : Nat := 11
def test5_Expected : Nat := 2

-- Test case 6: repeated digits 99 -> 9+9
def test6_n : Nat := 99
def test6_Expected : Nat := 18

-- Test case 7: typical multi-digit number 12345 -> 1+2+3+4+5
def test7_n : Nat := 12345
def test7_Expected : Nat := 15

-- Test case 8: power of ten 1000 -> 1+0+0+0
def test8_n : Nat := 1000
def test8_Expected : Nat := 1

-- Test case 9: larger number with varied digits
-- 987654321 -> 9+8+7+6+5+4+3+2+1 = 45
def test9_n : Nat := 987654321
def test9_Expected : Nat := 45
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
