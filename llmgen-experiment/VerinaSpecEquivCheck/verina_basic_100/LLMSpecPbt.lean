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
    TripleInt: compute three times an integer.
    Natural language breakdown:
    1. The input is a single integer x.
    2. The output is an integer result.
    3. The result must equal three times the input integer.
    4. In particular, when x = 0, the result is 0.
    5. There are no additional preconditions on x.
-/

section Specs
-- No helper definitions are needed; the required relationship is basic integer arithmetic.

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Int) : Prop :=
  result = 3 * x
end Specs

section Impl
method TripleInt (x : Int)
  return (result : Int)
  require precondition x
  ensures postcondition x result
  do
  pure 0  -- placeholder body only

prove_correct TripleInt by sorry
end Impl

section TestCases
-- Test case 1: example/edge case x = 0
-- Expect: 0

def test1_x : Int := 0
def test1_Expected : Int := 0

-- Test case 2: x = 1

def test2_x : Int := 1
def test2_Expected : Int := 3

-- Test case 3: x = -1

def test3_x : Int := (-1)
def test3_Expected : Int := (-3)

-- Test case 4: small positive

def test4_x : Int := 2
def test4_Expected : Int := 6

-- Test case 5: small negative

def test5_x : Int := (-2)
def test5_Expected : Int := (-6)

-- Test case 6: larger positive

def test6_x : Int := 10
def test6_Expected : Int := 30

-- Test case 7: larger negative

def test7_x : Int := (-10)
def test7_Expected : Int := (-30)

-- Test case 8: mixed sign check with nontrivial magnitude

def test8_x : Int := 12345
def test8_Expected : Int := 37035

-- Test case 9: mixed sign check with nontrivial negative magnitude

def test9_x : Int := (-12345)
def test9_Expected : Int := (-37035)
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
