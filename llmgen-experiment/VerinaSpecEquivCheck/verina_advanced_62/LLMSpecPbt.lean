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
    TrappingRainWater: compute the total rainwater trapped by a 1D elevation map.
    Natural language breakdown:
    1. The input is a list of non-negative integer heights; each height is the elevation of a bar of width 1.
    2. After raining, water can be trapped above an index only if there is a bar at least as high on its left
       and a bar at least as high on its right.
    3. For each index i, the maximum water level above it equals min(max height on the left up to i,
       max height on the right from i) minus the height at i.
    4. Negative water amounts are treated as 0 (no trapped water at that index).
    5. The total trapped water is the sum of the per-index trapped water amounts.
    6. If the list is empty or has fewer than 3 elements, the result is 0.
-/

section Specs
-- Helper: maximum height seen from the left up to (and including) index i.
-- Defined using take and foldl; for i out of range, it still yields a well-defined value.
def leftMaxUpTo (heights : List Int) (i : Nat) : Int :=
  (heights.take (i + 1)).foldl (init := (0 : Int)) max

-- Helper: maximum height seen from the right starting at index i.
def rightMaxFrom (heights : List Int) (i : Nat) : Int :=
  (heights.drop i).foldl (init := (0 : Int)) max

-- Helper: expected trapped water at index i, defaulting to 0 when i is out of range.
def expectedWaterAt (heights : List Int) (i : Nat) : Int :=
  match heights.get? i with
  | none => 0
  | some h =>
      max 0 (min (leftMaxUpTo heights i) (rightMaxFrom heights i) - h)

-- Preconditions: all heights are non-negative.
def precondition (heights : List Int) : Prop :=
  ∀ (i : Nat), i < heights.length → 0 ≤ (heights.get? i).getD 0

-- Postcondition: there exists a per-index water list whose elements match expectedWaterAt,
-- and result is the sum of these elements.
def postcondition (heights : List Int) (result : Int) : Prop :=
  (0 ≤ result) ∧
  (∃ (water : List Int),
    water.length = heights.length ∧
    water.sum = result ∧
    (∀ (i : Nat), i < heights.length → water.get? i = some (expectedWaterAt heights i)))
end Specs

section Impl
method TrappingRainWater (heights : List Int)
  return (result : Int)
  require precondition heights
  ensures postcondition heights result
  do
    pure 0

prove_correct TrappingRainWater by sorry
end Impl

section TestCases
-- Test case 1: classic example
-- heights = [0,1,0,2,1,0,1,3,2,1,2,1] => 6
-- (This is the canonical trapping-rain-water benchmark input.)
def test1_heights : List Int := [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]
def test1_Expected : Int := 6

-- Test case 2: empty list (degenerate)
def test2_heights : List Int := []
def test2_Expected : Int := 0

-- Test case 3: singleton list (degenerate)
def test3_heights : List Int := [0]
def test3_Expected : Int := 0

-- Test case 4: two elements (cannot trap)
def test4_heights : List Int := [1, 0]
def test4_Expected : Int := 0

-- Test case 5: strictly increasing (cannot trap)
def test5_heights : List Int := [0, 1, 2, 3, 4]
def test5_Expected : Int := 0

-- Test case 6: strictly decreasing (cannot trap)
def test6_heights : List Int := [4, 3, 2, 1, 0]
def test6_Expected : Int := 0

-- Test case 7: simple bowl
-- [2,0,2] traps 2

def test7_heights : List Int := [2, 0, 2]
def test7_Expected : Int := 2

-- Test case 8: multiple basins
-- [3,0,0,2,0,4] traps 10

def test8_heights : List Int := [3, 0, 0, 2, 0, 4]
def test8_Expected : Int := 10

-- Test case 9: all zeros

def test9_heights : List Int := [0, 0, 0]
def test9_Expected : Int := 0
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_heights result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
