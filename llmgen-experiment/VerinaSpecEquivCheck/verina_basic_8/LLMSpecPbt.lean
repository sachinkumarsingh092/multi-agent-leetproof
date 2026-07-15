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
    verina_basic_8: minimum of two integers
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The method returns an integer result.
    3. The result must be less than or equal to a.
    4. The result must be less than or equal to b.
    5. The result must be one of the inputs: result equals a or result equals b.
    6. If a = b, then either input may be returned (both choices are equal).
-/

section Specs
-- No input constraints are needed for taking the minimum of two integers.

def precondition (a : Int) (b : Int) : Prop :=
  True

-- The result is a lower bound of both inputs and is equal to one of them.
-- This uniquely characterizes the mathematical minimum, while allowing either
-- input to be returned in the equality case.
def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ (result = a ∨ result = b)
end Specs

section Impl
method MinInt (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  -- Placeholder body only (must typecheck)
  pure (min a b)

prove_correct MinInt by sorry
end Impl

section TestCases
-- Test case 1: typical distinct positive integers
def test1_a : Int := 7
def test1_b : Int := 3
def test1_Expected : Int := 3

-- Test case 2: already ordered (a smaller)
def test2_a : Int := 2
def test2_b : Int := 10
def test2_Expected : Int := 2

-- Test case 3: equal integers (either is acceptable; we pick that value)
def test3_a : Int := 5
def test3_b : Int := 5
def test3_Expected : Int := 5

-- Test case 4: includes zero
def test4_a : Int := 0
def test4_b : Int := 9
def test4_Expected : Int := 0

-- Test case 5: includes negative and positive
def test5_a : Int := -4
def test5_b : Int := 6
def test5_Expected : Int := -4

-- Test case 6: both negative
def test6_a : Int := -10
def test6_b : Int := -3
def test6_Expected : Int := -10

-- Test case 7: boundary-style small values (-1, 0)
def test7_a : Int := -1
def test7_b : Int := 0
def test7_Expected : Int := -1

-- Test case 8: boundary-style small values (0, 1)
def test8_a : Int := 0
def test8_b : Int := 1
def test8_Expected : Int := 0

-- Test case 9: larger magnitude mix
def test9_a : Int := 123456
def test9_b : Int := -789
def test9_Expected : Int := -789

-- Recommend to validate: ordering (a<b), ordering (b<a), equality (a=b)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_b result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
