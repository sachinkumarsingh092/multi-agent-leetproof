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
    IsPerfectSquare: Determine whether a given non-negative natural number is a perfect square.
    Natural language breakdown:
    1. The input n is a natural number, so it is non-negative.
    2. The output is a Boolean value.
    3. The output should be true exactly when there exists a natural number k such that k*k = n.
    4. The output should be false exactly when there is no natural number k such that k*k = n.
    5. Edge cases: 0 is a perfect square (0*0 = 0) and 1 is a perfect square (1*1 = 1).
-/

section Specs
-- Helper predicate: proposition-level notion of perfect square.
-- We use multiplication (k * k) as squaring.
def IsPerfectSquareProp (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsPerfectSquareProp n)
end Specs

section Impl
method IsPerfectSquare (n : Nat)
  return (result : Bool)
  require precondition (n)
  ensures postcondition (n) (result)
  do
    pure false  -- placeholder

prove_correct IsPerfectSquare by sorry
end Impl

section TestCases
-- Test case 1: n = 0 (boundary case)
def test1_n : Nat := 0
def test1_Expected : Bool := true

-- Test case 2: n = 1 (boundary case)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: n = 2 (not a square)
def test3_n : Nat := 2
def test3_Expected : Bool := false

-- Test case 4: n = 3 (not a square)
def test4_n : Nat := 3
def test4_Expected : Bool := false

-- Test case 5: n = 4 (2*2)
def test5_n : Nat := 4
def test5_Expected : Bool := true

-- Test case 6: n = 8 (not a square)
def test6_n : Nat := 8
def test6_Expected : Bool := false

-- Test case 7: n = 9 (3*3)
def test7_n : Nat := 9
def test7_Expected : Bool := true

-- Test case 8: n = 15 (not a square, near 16)
def test8_n : Nat := 15
def test8_Expected : Bool := false

-- Test case 9: n = 16 (4*4)
def test9_n : Nat := 16
def test9_Expected : Bool := true

-- Test case 10: n = 25 (5*5)
def test10_n : Nat := 25
def test10_Expected : Bool := true

-- Recommend to validate: test1_n, test2_n, test3_n
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Bool) :
  result ≠ test3_Expected →
  ¬ postcondition test3_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
