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
    IntAbs: Compute the absolute value of an integer.

    Natural language breakdown:
    1. The input is an integer x.
    2. The output is an integer result representing the magnitude of x with non-negative sign.
    3. If x is non-negative (0 ≤ x), then result equals x.
    4. If x is negative (x < 0), then result equals -x (the additive inverse of x).
    5. The function must handle negative inputs, zero, and positive inputs.
-/

section Specs
-- No helper definitions are required.

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int) : Prop :=
  (0 ≤ result) ∧
  ((0 ≤ x → result = x) ∧ (x < 0 → result = -x))
end Specs

section Impl
method IntAbs (x : Int)
  return (result : Int)
  require precondition x
  ensures postcondition x result
  do
  pure 0

prove_correct IntAbs by sorry
end Impl

section TestCases
-- Test case 1: x = 0
def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: x = 1
def test2_x : Int := 1
def test2_Expected : Int := 1

-- Test case 3: x = -1
def test3_x : Int := -1
def test3_Expected : Int := 1

-- Test case 4: a typical positive number
def test4_x : Int := 42
def test4_Expected : Int := 42

-- Test case 5: a typical negative number
def test5_x : Int := -42
def test5_Expected : Int := 42

-- Test case 6: a larger negative magnitude
def test6_x : Int := -123456
def test6_Expected : Int := 123456

-- Test case 7: a larger positive magnitude
def test7_x : Int := 987654
def test7_Expected : Int := 987654

-- Test case 8: another negative value
def test8_x : Int := -7
def test8_Expected : Int := 7
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
