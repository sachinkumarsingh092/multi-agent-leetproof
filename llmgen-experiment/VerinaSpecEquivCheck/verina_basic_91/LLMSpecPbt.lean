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
    SwapInts: swap two integer values.
    Natural language breakdown:
    1. The input consists of two integers X and Y.
    2. The output is an ordered pair of integers (Int × Int).
    3. The first component of the result equals the original Y.
    4. The second component of the result equals the original X.
    5. There are no required preconditions on X or Y.
-/

section Specs
def precondition (X : Int) (Y : Int) : Prop :=
  True

def postcondition (X : Int) (Y : Int) (result : Int × Int) : Prop :=
  result.1 = Y ∧ result.2 = X
end Specs

section Impl
method SwapInts (X : Int) (Y : Int)
  return (result : Int × Int)
  require precondition X Y
  ensures postcondition X Y result
  do
  pure (Y, X)  -- placeholder body

prove_correct SwapInts by sorry
end Impl

section TestCases
-- Test case 1: both positive
def test1_X : Int := 3
def test1_Y : Int := 7
def test1_Expected : Int × Int := (7, 3)

-- Test case 2: includes 0 boundary
def test2_X : Int := 0
def test2_Y : Int := 5
def test2_Expected : Int × Int := (5, 0)

-- Test case 3: includes negative boundary (-1)
def test3_X : Int := (-1)
def test3_Y : Int := 4
def test3_Expected : Int × Int := (4, -1)

-- Test case 4: both zero
def test4_X : Int := 0
def test4_Y : Int := 0
def test4_Expected : Int × Int := (0, 0)

-- Test case 5: both negative
def test5_X : Int := (-10)
def test5_Y : Int := (-20)
def test5_Expected : Int × Int := (-20, -10)

-- Test case 6: (1) boundary and negative
def test6_X : Int := 1
def test6_Y : Int := (-1)
def test6_Expected : Int × Int := (-1, 1)

-- Test case 7: large magnitude values
def test7_X : Int := 1000000
def test7_Y : Int := (-1000000)
def test7_Expected : Int × Int := (-1000000, 1000000)

-- Test case 8: same values
def test8_X : Int := 42
def test8_Y : Int := 42
def test8_Expected : Int × Int := (42, 42)
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Int × Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_X test8_Y result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
