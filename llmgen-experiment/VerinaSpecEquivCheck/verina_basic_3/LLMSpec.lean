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
    DivisibleBy11: Determine whether a given integer is divisible by 11.
    Natural language breakdown:
    1. The input is an integer n.
    2. The output is a Boolean.
    3. The output should be true exactly when 11 divides n (i.e., there exists an integer k with n = 11 * k).
    4. The output should be false exactly when 11 does not divide n.
-/

section Specs
-- No helper functions are required; Mathlib/Lean provides integer divisibility via (∣).

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ (11 : Int) ∣ n) ∧
  (result = false ↔ ¬ ((11 : Int) ∣ n))
end Specs

section Impl
method DivisibleBy11 (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
  pure true

end Impl

section TestCases
-- Test case 1: n = 11 is divisible by 11
def test1_n : Int := 11
def test1_Expected : Bool := true

-- Test case 2: n = 0 is divisible by 11
def test2_n : Int := 0
def test2_Expected : Bool := true

-- Test case 3: n = 1 is not divisible by 11
def test3_n : Int := 1
def test3_Expected : Bool := false

-- Test case 4: n = -1 is not divisible by 11
def test4_n : Int := -1
def test4_Expected : Bool := false

-- Test case 5: n = -11 is divisible by 11
def test5_n : Int := -11
def test5_Expected : Bool := true

-- Test case 6: n = 22 is divisible by 11
def test6_n : Int := 22
def test6_Expected : Bool := true

-- Test case 7: n = 10 is not divisible by 11
def test7_n : Int := 10
def test7_Expected : Bool := false

-- Test case 8: n = 121 is divisible by 11
def test8_n : Int := 121
def test8_Expected : Bool := true

-- Test case 9: n = 120 is not divisible by 11
def test9_n : Int := 120
def test9_Expected : Bool := false
end TestCases
