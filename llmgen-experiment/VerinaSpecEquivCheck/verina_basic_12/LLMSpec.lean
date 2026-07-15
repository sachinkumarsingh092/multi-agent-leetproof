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
    CubeSurfaceArea: compute the surface area of a cube from the length of one edge.

    Natural language breakdown:
    1. The input `size` is a natural number representing the length of one edge of a cube.
    2. The surface area of a cube equals 6 times the area of one face.
    3. The area of one square face with side length `size` is `size * size`.
    4. Therefore the required result is `6 * size * size` as a natural number.
-/

section Specs
-- No preconditions are needed because the input is a Nat (already nonnegative).
-- Kept as a separate definition to match the SpecDSL structure.
def precondition (size : Nat) : Prop :=
  True

-- The result is exactly the cube surface area using the standard formula.
def postcondition (size : Nat) (result : Nat) : Prop :=
  result = 6 * size * size
end Specs

section Impl
method CubeSurfaceArea (size : Nat)
  return (result : Nat)
  require precondition size
  ensures postcondition size result
  do
  -- Placeholder implementation only.
  pure 0

end Impl

section TestCases
-- Test case 1: edge length 1
-- Surface area = 6 * 1^2 = 6
def test1_size : Nat := 1
def test1_Expected : Nat := 6

-- Test case 2: edge length 0 (degenerate cube)
-- Surface area = 0
def test2_size : Nat := 0
def test2_Expected : Nat := 0

-- Test case 3: edge length 2
def test3_size : Nat := 2
def test3_Expected : Nat := 24

-- Test case 4: edge length 3
def test4_size : Nat := 3
def test4_Expected : Nat := 54

-- Test case 5: edge length 4
def test5_size : Nat := 4
def test5_Expected : Nat := 96

-- Test case 6: edge length 7
def test6_size : Nat := 7
def test6_Expected : Nat := 294

-- Test case 7: edge length 10
def test7_size : Nat := 10
def test7_Expected : Nat := 600

-- Test case 8: larger edge length 100
def test8_size : Nat := 100
def test8_Expected : Nat := 60000
end TestCases
