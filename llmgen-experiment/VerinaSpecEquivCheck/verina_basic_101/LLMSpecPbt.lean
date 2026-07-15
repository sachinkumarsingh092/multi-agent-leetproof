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
    TripleInt: compute the triple of a given integer.
    Natural language breakdown:
    1. The input is a single integer x.
    2. The output is an integer result.
    3. The output must be exactly three times the input.
    4. This means result = 3 * x using integer multiplication.
    5. The specification places no restrictions on x (it may be negative, zero, or positive).
-/

section Specs
-- No helper functions are needed: the intended result is directly characterized by Int arithmetic.

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int) : Prop :=
  result = (3 * x)
end Specs

section Impl
method TripleInt (x : Int)
  return (result : Int)
  require precondition x
  ensures postcondition x result
  do
  -- Placeholder body only; correctness proof is provided separately.
  pure 0

prove_correct TripleInt by sorry
end Impl

section TestCases
-- Test case 1: zero
-- Edge case: x = 0

def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: one
-- Edge case: x = 1

def test2_x : Int := 1
def test2_Expected : Int := 3

-- Test case 3: negative one
-- Edge case: x = -1

def test3_x : Int := (-1)
def test3_Expected : Int := (-3)

-- Test case 4: small positive

def test4_x : Int := 2
def test4_Expected : Int := 6

-- Test case 5: small negative

def test5_x : Int := (-5)
def test5_Expected : Int := (-15)

-- Test case 6: medium positive

def test6_x : Int := 7
def test6_Expected : Int := 21

-- Test case 7: larger positive

def test7_x : Int := 42
def test7_Expected : Int := 126

-- Test case 8: larger negative

def test8_x : Int := (-123)
def test8_Expected : Int := (-369)

-- Test case 9: very large magnitude (still within Int)

def test9_x : Int := 1000000
def test9_Expected : Int := 3000000
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
