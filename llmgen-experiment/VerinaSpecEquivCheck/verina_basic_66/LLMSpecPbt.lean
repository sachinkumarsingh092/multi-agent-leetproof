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
    IsEven: Determine whether an integer is even.
    Natural language breakdown:
    1. The input is a single integer x.
    2. The output is a boolean value.
    3. The output is true exactly when x is divisible by 2 with no remainder.
    4. Equivalently, the output is true exactly when x mod 2 equals 0.
    5. The method must behave correctly for all integers (negative, zero, and positive).
-/

section Specs
def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Bool) : Prop :=
  (result = true ↔ x % 2 = 0)
end Specs

section Impl
method IsEven (x : Int)
  return (result : Bool)
  require precondition x
  ensures postcondition x result
  do
  pure true  -- placeholder body

prove_correct IsEven by sorry
end Impl

section TestCases
-- Test case 1: x = 0 (edge case)
def test1_x : Int := 0
def test1_Expected : Bool := true

-- Test case 2: x = 1 (edge case)
def test2_x : Int := 1
def test2_Expected : Bool := false

-- Test case 3: x = -1 (edge case)
def test3_x : Int := (-1)
def test3_Expected : Bool := false

-- Test case 4: small positive even
def test4_x : Int := 2
def test4_Expected : Bool := true

-- Test case 5: small positive odd
def test5_x : Int := 3
def test5_Expected : Bool := false

-- Test case 6: small negative even
def test6_x : Int := (-2)
def test6_Expected : Bool := true

-- Test case 7: small negative odd
def test7_x : Int := (-3)
def test7_Expected : Bool := false

-- Test case 8: larger positive even
def test8_x : Int := 100
def test8_Expected : Bool := true

-- Test case 9: larger negative odd
def test9_x : Int := (-101)
def test9_Expected : Bool := false

-- Recommend to validate: 0, 1, -1
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1' (result : Bool) :
  result ≠ test1_Expected →
  ¬ postcondition test1_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
