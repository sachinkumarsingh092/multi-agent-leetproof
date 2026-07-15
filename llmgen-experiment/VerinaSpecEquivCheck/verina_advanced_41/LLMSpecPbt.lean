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
    MaxOfThreeInts: Find the maximum among three given integers.

    Natural language breakdown:
    1. Inputs are three integers a, b, and c.
    2. The output is an integer result.
    3. The result must be greater than or equal to each of the three inputs.
    4. The result must be equal to one of the input integers (it is not a new value).
    5. The result must be the least integer that is an upper bound of {a,b,c}:
       if any integer x is at least a, b, and c, then result ≤ x.
-/

section Specs
-- No special preconditions are required for Int inputs.
def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

-- Postcondition: result is the least upper bound of {a,b,c} and is achieved by one of them.
def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  (a ≤ result) ∧
  (b ≤ result) ∧
  (c ≤ result) ∧
  (result = a ∨ result = b ∨ result = c) ∧
  (∀ x : Int, a ≤ x → b ≤ x → c ≤ x → result ≤ x)
end Specs

section Impl
method MaxOfThreeInts (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
  -- Placeholder body only; correctness is established separately.
  pure a

prove_correct MaxOfThreeInts by sorry
end Impl

section TestCases
-- Test case 1: typical ascending inputs
-- max(1,2,3) = 3

def test1_a : Int := 1
def test1_b : Int := 2
def test1_c : Int := 3
def test1_Expected : Int := 3

-- Test case 2: max is first argument

def test2_a : Int := 10
def test2_b : Int := 0
def test2_c : Int := -5
def test2_Expected : Int := 10

-- Test case 3: max is second argument

def test3_a : Int := -1
def test3_b : Int := 7
def test3_c : Int := 3
def test3_Expected : Int := 7

-- Test case 4: all equal

def test4_a : Int := 5
def test4_b : Int := 5
def test4_c : Int := 5
def test4_Expected : Int := 5

-- Test case 5: two-way tie for max (a and b)

def test5_a : Int := 4
def test5_b : Int := 4
def test5_c : Int := 2
def test5_Expected : Int := 4

-- Test case 6: includes 0 as max

def test6_a : Int := -3
def test6_b : Int := 0
def test6_c : Int := -1
def test6_Expected : Int := 0

-- Test case 7: includes boundary values -1, 0, 1

def test7_a : Int := -1
def test7_b : Int := 0
def test7_c : Int := 1
def test7_Expected : Int := 1

-- Test case 8: all negative

def test8_a : Int := -10
def test8_b : Int := -2
def test8_c : Int := -30
def test8_Expected : Int := -2

-- Test case 9: large magnitude values

def test9_a : Int := 1000000
def test9_b : Int := -1000000
def test9_c : Int := 999999
def test9_Expected : Int := 1000000
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a test9_b test9_c result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
