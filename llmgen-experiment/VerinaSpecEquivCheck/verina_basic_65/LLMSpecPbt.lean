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
    IntegerSqrt: compute the integer square root of a natural number.
    Natural language breakdown:
    1. The input N is a natural number.
    2. The output r is a natural number.
    3. The result r must be a lower bound on the real square root in the sense that r*r ≤ N.
    4. The result r must be maximal with that property, equivalently N < (r+1)*(r+1).
    5. Edge cases such as N = 0 and N = 1 must satisfy the same inequalities.
-/

section Specs
-- No helper functions are required: the specification is expressed directly
-- using multiplication and ordering on Nat.

def precondition (N : Nat) : Prop :=
  True

def postcondition (N : Nat) (result : Nat) : Prop :=
  result * result ≤ N ∧
  N < (result + 1) * (result + 1)
end Specs

section Impl
method IntegerSqrt (N : Nat)
  return (result : Nat)
  require precondition N
  ensures postcondition N result
  do
  pure 0

prove_correct IntegerSqrt by sorry
end Impl

section TestCases
-- Test case 1: edge case N = 0
def test1_N : Nat := 0
def test1_Expected : Nat := 0

-- Test case 2: edge case N = 1
def test2_N : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: small non-square
def test3_N : Nat := 2
def test3_Expected : Nat := 1

-- Test case 4: small non-square
def test4_N : Nat := 3
def test4_Expected : Nat := 1

-- Test case 5: perfect square
def test5_N : Nat := 4
def test5_Expected : Nat := 2

-- Test case 6: larger non-square just below a square
def test6_N : Nat := 15
def test6_Expected : Nat := 3

-- Test case 7: perfect square
def test7_N : Nat := 16
def test7_Expected : Nat := 4

-- Test case 8: larger non-square just above a square
def test8_N : Nat := 17
def test8_Expected : Nat := 4

-- Test case 9: another perfect square
def test9_N : Nat := 25
def test9_Expected : Nat := 5
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_N result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
