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
    IsPowerOfTwo: Determine whether a given integer is a power of two.

    Natural language breakdown:
    1. The input is a single integer n.
    2. n is a power of two exactly when there exists a natural exponent k such that n = 2^k.
    3. Only positive integers can be powers of two; zero and negative integers are not powers of two.
    4. The output is a boolean result.
    5. The method returns true iff n is a (positive) power of two; otherwise it returns false.
-/

section Specs
-- A mathematical predicate describing when an integer is a (positive) power of two.
-- We use a natural exponent because integer exponentiation `(^)` takes a `Nat` exponent.
def IsPowerOfTwo (n : Int) : Prop :=
  (0 < n) ∧ (∃ k : Nat, n = (2 : Int) ^ k)

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ IsPowerOfTwo n)
end Specs

section Impl
method IsPowerOfTwoBool (n : Int)
  return (result : Bool)
  require precondition n
  ensures postcondition n result
  do
    pure false  -- placeholder body

end Impl

section TestCases
-- Test case 1: n = 1 (2^0)
def test1_n : Int := 1
def test1_Expected : Bool := true

-- Test case 2: n = 0 (not a power of two)
def test2_n : Int := 0
def test2_Expected : Bool := false

-- Test case 3: n = -1 (negative, not a power of two)
def test3_n : Int := -1
def test3_Expected : Bool := false

-- Test case 4: n = 2 (2^1)
def test4_n : Int := 2
def test4_Expected : Bool := true

-- Test case 5: n = 3 (not a power of two)
def test5_n : Int := 3
def test5_Expected : Bool := false

-- Test case 6: n = 4 (2^2)
def test6_n : Int := 4
def test6_Expected : Bool := true

-- Test case 7: n = 8 (2^3)
def test7_n : Int := 8
def test7_Expected : Bool := true

-- Test case 8: n = 12 (not a power of two)
def test8_n : Int := 12
def test8_Expected : Bool := false

-- Test case 9: n = 16 (2^4)
def test9_n : Int := 16
def test9_Expected : Bool := true
end TestCases
