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
    TwiceAndFourTimes: compute the pair (2*x, 4*x) from an integer input x.
    Natural language breakdown:
    1. The input is a single integer x.
    2. The output is a pair (a, b) of integers.
    3. The first component a equals twice x.
    4. The second component b equals four times x.
    5. The method is defined for all integers (no preconditions).
-/

section Specs
def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : (Int × Int)) : Prop :=
  result.1 = (2 : Int) * x ∧
  result.2 = (4 : Int) * x
end Specs

section Impl
method TwiceAndFourTimes (x : Int)
  return (result : (Int × Int))
  require precondition x
  ensures postcondition x result
  do
  pure (0, 0)  -- placeholder

prove_correct TwiceAndFourTimes by sorry
end Impl

section TestCases
-- Test case 1: x = 0 (edge case)
def test1_x : Int := 0
def test1_Expected : (Int × Int) := ((2 : Int) * test1_x, (4 : Int) * test1_x)

-- Test case 2: x = 1 (edge case)
def test2_x : Int := 1
def test2_Expected : (Int × Int) := ((2 : Int) * test2_x, (4 : Int) * test2_x)

-- Test case 3: x = -1 (edge case)
def test3_x : Int := -1
def test3_Expected : (Int × Int) := ((2 : Int) * test3_x, (4 : Int) * test3_x)

-- Test case 4: x = 2 (small positive)
def test4_x : Int := 2
def test4_Expected : (Int × Int) := ((2 : Int) * test4_x, (4 : Int) * test4_x)

-- Test case 5: x = -2 (small negative)
def test5_x : Int := -2
def test5_Expected : (Int × Int) := ((2 : Int) * test5_x, (4 : Int) * test5_x)

-- Test case 6: x = 7 (typical)
def test6_x : Int := 7
def test6_Expected : (Int × Int) := ((2 : Int) * test6_x, (4 : Int) * test6_x)

-- Test case 7: x = -7 (typical negative)
def test7_x : Int := -7
def test7_Expected : (Int × Int) := ((2 : Int) * test7_x, (4 : Int) * test7_x)

-- Test case 8: x = 100000 (larger magnitude)
def test8_x : Int := 100000
def test8_Expected : (Int × Int) := ((2 : Int) * test8_x, (4 : Int) * test8_x)

-- Test case 9: x = -100000 (larger magnitude negative)
def test9_x : Int := -100000
def test9_Expected : (Int × Int) := ((2 : Int) * test9_x, (4 : Int) * test9_x)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : (Int × Int)) :
  result ≠ test9_Expected →
  ¬ postcondition test9_x result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
