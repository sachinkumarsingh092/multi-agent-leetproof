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
    SwapTwoIntegers: Swap the values of two integers.
    Natural language breakdown:
    1. The input consists of two integers X and Y.
    2. The output is a pair (Int × Int).
    3. The first component of the output must equal the original Y.
    4. The second component of the output must equal the original X.
    5. There are no restrictions on X or Y: they may be negative, zero, or positive.
-/

section Specs
-- No helper functions are required: the specification is fully described
-- by properties of the pair projections `fst` and `snd`.

def precondition (X : Int) (Y : Int) : Prop :=
  True

def postcondition (X : Int) (Y : Int) (result : (Int × Int)) : Prop :=
  result.fst = Y ∧ result.snd = X
end Specs

section Impl
method SwapTwoIntegers (X : Int) (Y : Int)
  return (result : (Int × Int))
  require precondition X Y
  ensures postcondition X Y result
  do
  pure (Y, X)  -- placeholder body

prove_correct SwapTwoIntegers by sorry
end Impl

section TestCases
-- Test case 1: basic positive integers
def test1_X : Int := 3
def test1_Y : Int := 7
def test1_Expected : (Int × Int) := (7, 3)

-- Test case 2: includes zero
def test2_X : Int := 0
def test2_Y : Int := 5
def test2_Expected : (Int × Int) := (5, 0)

-- Test case 3: both zero
def test3_X : Int := 0
def test3_Y : Int := 0
def test3_Expected : (Int × Int) := (0, 0)

-- Test case 4: both negative
def test4_X : Int := (-4)
def test4_Y : Int := (-9)
def test4_Expected : (Int × Int) := (-9, -4)

-- Test case 5: mixed sign
def test5_X : Int := (-1)
def test5_Y : Int := 2
def test5_Expected : (Int × Int) := (2, -1)

-- Test case 6: boundary-style small values -1, 0, 1
def test6_X : Int := 1
def test6_Y : Int := (-1)
def test6_Expected : (Int × Int) := (-1, 1)

-- Test case 7: equal inputs
def test7_X : Int := 42
def test7_Y : Int := 42
def test7_Expected : (Int × Int) := (42, 42)

-- Test case 8: larger magnitude values
def test8_X : Int := 1000000000
def test8_Y : Int := (-1000000000)
def test8_Expected : (Int × Int) := (-1000000000, 1000000000)

-- Test case 9: swap where second is zero and first is negative
def test9_X : Int := (-123)
def test9_Y : Int := 0
def test9_Expected : (Int × Int) := (0, -123)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : (Int × Int)) :
  result ≠ test9_Expected →
  ¬ postcondition test9_X test9_Y result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
