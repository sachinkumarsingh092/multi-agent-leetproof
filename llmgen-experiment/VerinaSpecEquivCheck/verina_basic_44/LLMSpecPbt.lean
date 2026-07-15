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
    OddIndexHoldsOdd: Verify if every odd index in an array of integers holds an odd integer.
    Natural language breakdown:
    1. The input is an array `a` of integers.
    2. An index `i` is relevant exactly when it is within bounds (`i < a.size`) and `i` is odd.
    3. The property holds when, for every relevant index `i`, the element `a[i]!` is an odd integer.
    4. The method returns `true` iff the property holds; otherwise it returns `false`.
    5. There are no preconditions; the method must behave on all integer arrays.
-/

section Specs
-- Helper predicate: all elements at odd indices are odd.
-- We express index oddness using a simple modular condition on Nat to avoid relying on `Nat.Odd`.
-- For values, we use `Odd` on `Int`.

def oddIndex (i : Nat) : Prop :=
  i % 2 = 1

def oddIndicesHoldOdd (a : Array Int) : Prop :=
  ∀ (i : Nat), i < a.size → oddIndex i → Odd (a[i]!)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ oddIndicesHoldOdd a)
end Specs

section Impl
method OddIndexHoldsOdd (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  -- placeholder body only
  pure true

prove_correct OddIndexHoldsOdd by sorry
end Impl

section TestCases
-- Test case 1: typical passing case
def test1_a : Array Int := #[1, 3, 5]
def test1_Expected : Bool := true

-- Test case 2: odd index 1 contains an even number -> fails
def test2_a : Array Int := #[1, 4, 5]
def test2_Expected : Bool := false

-- Test case 3: empty array (vacuously true)
def test3_a : Array Int := #[]
def test3_Expected : Bool := true

-- Test case 4: singleton array (no odd indices)
def test4_a : Array Int := #[2]
def test4_Expected : Bool := true

-- Test case 5: size 2, index 1 is odd and holds odd -> true
def test5_a : Array Int := #[0, 7]
def test5_Expected : Bool := true

-- Test case 6: size 2, index 1 is odd and holds even -> false
def test6_a : Array Int := #[0, 6]
def test6_Expected : Bool := false

-- Test case 7: larger passing case with multiple odd indices
-- indices 1 and 3 are odd; both values are odd
def test7_a : Array Int := #[10, 1, 12, 9, 14]
def test7_Expected : Bool := true

-- Test case 8: larger failing case at index 3
-- index 3 is odd but value 8 is even
def test8_a : Array Int := #[10, 1, 12, 8, 14]
def test8_Expected : Bool := false

-- Test case 9: negative odd values should count as odd
-- index 1 is odd and value -3 is odd
def test9_a : Array Int := #[2, -3, 4]
def test9_Expected : Bool := true

-- Recommend to validate: empty arrays, singleton arrays, arrays with negative values at odd indices
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Bool) :
  result ≠ test9_Expected →
  ¬ postcondition test9_a result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
