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
    AverageTwoIntegers: compute an integer average of two integers using integer division.
    Natural language breakdown:
    1. Inputs are two integers a and b.
    2. Let s = a + b be their sum.
    3. The output result is an integer intended to represent the arithmetic mean (a + b) / 2 under integer division.
    4. As an integer-division average, result should be the greatest integer such that 2*result ≤ s.
    5. Equivalently, s is strictly less than 2*(result + 1).
    6. Additionally, the required rounding boundary must hold: (s - 1) ≤ 2*result ≤ (s + 1).
    7. No additional input constraints are required.
-/

section Specs
-- Helper predicate: result is the floor of s/2, expressed without using division.
-- This uniquely determines result for all integers s.
def isFloorHalf (s : Int) (result : Int) : Prop :=
  (2 * result ≤ s) ∧ (s < 2 * (result + 1))

def precondition (a : Int) (b : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  let s : Int := a + b
  isFloorHalf s result ∧
  (s - 1 ≤ 2 * result) ∧ (2 * result ≤ s + 1)
end Specs

section Impl
method AverageTwoIntegers (a : Int) (b : Int)
  return (result : Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure 0

prove_correct AverageTwoIntegers by sorry
end Impl

section TestCases
-- Test case 1: both zero
-- sum = 0, average = 0

def test1_a : Int := 0
def test1_b : Int := 0
def test1_Expected : Int := 0

-- Test case 2: zero and one (odd sum, floor-half behavior)
-- sum = 1, floor(1/2) = 0

def test2_a : Int := 0
def test2_b : Int := 1
def test2_Expected : Int := 0

-- Test case 3: both one
-- sum = 2, average = 1

def test3_a : Int := 1
def test3_b : Int := 1
def test3_Expected : Int := 1

-- Test case 4: -1 and 1
-- sum = 0, average = 0

def test4_a : Int := -1
def test4_b : Int := 1
def test4_Expected : Int := 0

-- Test case 5: -1 and 0 (negative odd sum)
-- sum = -1, floor(-1/2) = -1

def test5_a : Int := -1
def test5_b : Int := 0
def test5_Expected : Int := -1

-- Test case 6: both negative
-- sum = -7, floor(-7/2) = -4

def test6_a : Int := -3
def test6_b : Int := -4
def test6_Expected : Int := -4

-- Test case 7: typical positive odd sum
-- sum = 11, floor(11/2) = 5

def test7_a : Int := 5
def test7_b : Int := 6
def test7_Expected : Int := 5

-- Test case 8: symmetric cancellation
-- sum = 0, average = 0

def test8_a : Int := 10
def test8_b : Int := -10
def test8_Expected : Int := 0

-- Test case 9: larger gap, odd sum
-- sum = 3, floor(3/2) = 1

def test9_a : Int := 100
def test9_b : Int := -97
def test9_Expected : Int := 1
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
