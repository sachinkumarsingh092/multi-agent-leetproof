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
    PowerOfFourBool: determine whether a natural number is a power of four.
    Natural language breakdown:
    1. Input is a natural number n.
    2. A natural number n is a power of four exactly when there exists a natural number x such that n = 4 ^ x.
    3. The method returns a boolean result.
    4. The result must be true exactly for those n that are powers of four (including 4 ^ 0 = 1).
    5. The result must be false exactly for those n that are not powers of four (in particular, 0 is not a power of four).
-/

section Specs
-- Helper predicate: n is a power of four in the mathematical sense.
def IsPowerOfFour (n : Nat) : Prop :=
  ∃ (x : Nat), n = 4 ^ x

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsPowerOfFour n) ∧
  (result = false ↔ ¬ IsPowerOfFour n)
end Specs

section Impl
method PowerOfFourBool (n : Nat)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure false  -- placeholder

prove_correct PowerOfFourBool by sorry
end Impl

section TestCases
-- Test case 1: n = 0 (edge case; not a power of four)
def test1_n : Nat := 0
def test1_Expected : Bool := false

-- Test case 2: n = 1 = 4^0 (smallest power of four)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: n = 4 = 4^1
def test3_n : Nat := 4
def test3_Expected : Bool := true

-- Test case 4: n = 16 = 4^2
def test4_n : Nat := 16
def test4_Expected : Bool := true

-- Test case 5: n = 2 (power of two but not power of four)
def test5_n : Nat := 2
def test5_Expected : Bool := false

-- Test case 6: n = 8 (not a power of four)
def test6_n : Nat := 8
def test6_Expected : Bool := false

-- Test case 7: n = 64 = 4^3
def test7_n : Nat := 64
def test7_Expected : Bool := true

-- Test case 8: n = 12 (arbitrary non-power)
def test8_n : Nat := 12
def test8_Expected : Bool := false

-- Test case 9: n = 256 = 4^4
def test9_n : Nat := 256
def test9_Expected : Bool := true

-- Recommend to validate: boundary values (0, 1), small powers (4, 16), near-misses (2, 8), larger power (256)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Bool) :
  result ≠ test8_Expected →
  ¬ postcondition test8_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
