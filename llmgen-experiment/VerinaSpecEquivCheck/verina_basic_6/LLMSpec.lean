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
    verina_basic_6: Find the minimum among three given integers.

    Natural language breakdown:
    1. The inputs are three integers a, b, and c.
    2. The output is an integer result.
    3. The result must be less than or equal to each of a, b, and c.
    4. The result must be equal to one of the inputs (a, b, or c).
    5. There are no domain restrictions on the integers.
-/

section Specs
-- No helper functions are required; the minimum is characterized by order and membership.

def precondition (a : Int) (b : Int) (c : Int) : Prop :=
  True

def postcondition (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  result ≤ a ∧
  result ≤ b ∧
  result ≤ c ∧
  (result = a ∨ result = b ∨ result = c)
end Specs

section Impl
method MinOfThree (a : Int) (b : Int) (c : Int)
  return (result : Int)
  require precondition a b c
  ensures postcondition a b c result
  do
  pure 0  -- placeholder body for type checking

end Impl

section TestCases
-- Test case 1: mixed positive values
def test1_a : Int := 3
def test1_b : Int := 1
def test1_c : Int := 2
def test1_Expected : Int := 1

-- Test case 2: includes negatives
def test2_a : Int := -5
def test2_b : Int := 7
def test2_c : Int := 0
def test2_Expected : Int := -5

-- Test case 3: all equal
def test3_a : Int := 4
def test3_b : Int := 4
def test3_c : Int := 4
def test3_Expected : Int := 4

-- Test case 4: two equal minima
def test4_a : Int := 1
def test4_b : Int := 1
def test4_c : Int := 9
def test4_Expected : Int := 1

-- Test case 5: already increasing order
def test5_a : Int := 0
def test5_b : Int := 1
def test5_c : Int := 2
def test5_Expected : Int := 0

-- Test case 6: already decreasing order
def test6_a : Int := 10
def test6_b : Int := 0
def test6_c : Int := -1
def test6_Expected : Int := -1

-- Test case 7: minimum is the third argument
def test7_a : Int := 8
def test7_b : Int := 6
def test7_c : Int := 2
def test7_Expected : Int := 2

-- Test case 8: minimum is zero with negative present? (checks ties around 0)
def test8_a : Int := -1
def test8_b : Int := 0
def test8_c : Int := 0
def test8_Expected : Int := -1

-- Test case 9: large magnitude values
def test9_a : Int := 1000000
def test9_b : Int := -1000000
def test9_c : Int := 999999
def test9_Expected : Int := -1000000
end TestCases
