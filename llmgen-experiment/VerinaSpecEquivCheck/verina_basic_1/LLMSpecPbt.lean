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
    OppositeSigns: Determine whether two given integers have opposite signs
    Natural language breakdown:
    1. Inputs are two integers a and b.
    2. An integer is positive exactly when it is greater than 0.
    3. An integer is negative exactly when it is less than 0.
    4. Zero is neither positive nor negative.
    5. The result should be true exactly when one input is positive and the other is negative.
    6. If either input is 0, the result must be false.
    7. If both inputs are positive, the result must be false.
    8. If both inputs are negative, the result must be false.
-/

section Specs
-- We keep the specification purely relational over Int order comparisons.

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Bool) : Prop :=
  result = true ↔ ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0))
end Specs

section Impl
method OppositeSigns (a : Int) (b : Int)
  return (result : Bool)
  require precondition a b
  ensures postcondition a b result
  do
  pure false

prove_correct OppositeSigns by sorry
end Impl

section TestCases
-- Test case 1: typical opposite signs
def test1_a : Int := 5
def test1_b : Int := (-7)
def test1_Expected : Bool := true

-- Test case 2: opposite signs swapped
def test2_a : Int := (-1)
def test2_b : Int := 1
def test2_Expected : Bool := true

-- Test case 3: both positive
def test3_a : Int := 2
def test3_b : Int := 3
def test3_Expected : Bool := false

-- Test case 4: both negative
def test4_a : Int := (-2)
def test4_b : Int := (-3)
def test4_Expected : Bool := false

-- Test case 5: left is zero
def test5_a : Int := 0
def test5_b : Int := (-3)
def test5_Expected : Bool := false

-- Test case 6: right is zero
def test6_a : Int := 7
def test6_b : Int := 0
def test6_Expected : Bool := false

-- Test case 7: both zero
def test7_a : Int := 0
def test7_b : Int := 0
def test7_Expected : Bool := false

-- Test case 8: boundary around -1,0,1 (negative and positive)
def test8_a : Int := (-1)
def test8_b : Int := 2
def test8_Expected : Bool := true

-- Test case 9: another non-opposite case (negative with negative)
def test9_a : Int := (-1)
def test9_b : Int := (-1)
def test9_Expected : Bool := false
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Bool) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
