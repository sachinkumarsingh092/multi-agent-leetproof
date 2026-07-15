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
    191. Number of 1 Bits: return the number of set bits in the binary representation of a natural number.
    **Important: complexity should be O(k) time and O(1) space**, where k is the number of set bits in n.
    Natural language breakdown:
    1. Input is a natural number n (non-negative integer).
    2. Each natural number has a binary representation with bits indexed from 0 (least-significant bit) upward.
    3. A bit is set iff it equals 1, i.e. iff n.testBit i = true for that index i.
    4. The required output is the count of indices i for which the bit is set.
    5. For i ≥ n.size (the number of bits needed to represent n), n.testBit i is false, so counting up to n.size suffices.
    6. Edge cases: n = 0 has zero set bits; powers of two have exactly one set bit.
-/

section Specs
-- We count set bits among indices 0,1,...,n.size-1.
-- For i ≥ n.size, Nat.testBit is false, so the count over this range is the Hamming weight.

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Nat) : Prop :=
  result = ((Finset.range n.size).filter (fun (i : Nat) => n.testBit i = true)).card ∧
  result ≤ n.size
end Specs

section Impl
method NumberOf1Bits (n : Nat)
  return (result : Nat)
  require precondition n
  ensures postcondition n result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1
def test1_n : Nat := 11
def test1_Expected : Nat := 3

-- Test case 2: Example 2
def test2_n : Nat := 128
def test2_Expected : Nat := 1

-- Test case 3: Example 3
def test3_n : Nat := 2147483645
def test3_Expected : Nat := 30

-- Test case 4: boundary n = 0
def test4_n : Nat := 0
def test4_Expected : Nat := 0

-- Test case 5: boundary n = 1
def test5_n : Nat := 1
def test5_Expected : Nat := 1

-- Test case 6: all low bits set (15 = 0b1111)
def test6_n : Nat := 15
def test6_Expected : Nat := 4

-- Test case 7: power of two (16 = 0b10000)
def test7_n : Nat := 16
def test7_Expected : Nat := 1

-- Test case 8: all bits set in a byte (255 = 0b11111111)
def test8_n : Nat := 255
def test8_Expected : Nat := 8

-- Test case 9: all bits set in 10 bits (1023 = 0b1111111111)
def test9_n : Nat := 1023
def test9_Expected : Nat := 10
end TestCases
