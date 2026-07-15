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
    MajorityElement: find the majority element in a list of natural numbers.
    Natural language breakdown:
    1. Input is a list of natural numbers `xs`.
    2. Let `n = xs.length`.
    3. For a value `v`, its number of occurrences in `xs` is `xs.count v`.
    4. A value `v` is a majority element of `xs` if `xs.count v > n / 2` where `/` is floor division on `Nat`.
    5. The input is guaranteed to contain a majority element, so `xs` is nonempty and some value satisfies the majority inequality.
    6. Output is the (unique) value that appears more than half of the time.
-/

section Specs
-- A value is a majority element of a list if it appears strictly more than half of the list length.
def IsMajority (xs : List Nat) (v : Nat) : Prop :=
  xs.count v > xs.length / 2

-- Precondition: a majority element exists (which also implies non-emptiness).
def precondition (xs : List Nat) : Prop :=
  ∃ m : Nat, IsMajority xs m

-- Postcondition: `result` is a majority element, and any majority element must equal `result`
-- (so the output is uniquely determined by the mathematical property).
def postcondition (xs : List Nat) (result : Nat) : Prop :=
  IsMajority xs result ∧
  (∀ y : Nat, IsMajority xs y → y = result)
end Specs

section Impl
method MajorityElement (xs : List Nat)
  return (result : Nat)
  require precondition xs
  ensures postcondition xs result
  do
  -- Placeholder implementation only
  pure 0

end Impl

section TestCases
-- Test case 1: simple majority in a short list
def test1_xs : List Nat := [2, 2, 1]
def test1_Expected : Nat := 2

-- Test case 2: singleton list (majority is the only element)
def test2_xs : List Nat := [0]
def test2_Expected : Nat := 0

-- Test case 3: all elements equal
def test3_xs : List Nat := [5, 5, 5, 5]
def test3_Expected : Nat := 5

-- Test case 4: odd length, clear majority
def test4_xs : List Nat := [1, 2, 1, 1, 3]
def test4_Expected : Nat := 1

-- Test case 5: even length, majority just above half
def test5_xs : List Nat := [4, 4, 4, 2, 2, 4]
def test5_Expected : Nat := 4

-- Test case 6: includes 0 and 1, majority is 0
def test6_xs : List Nat := [0, 1, 0, 0]
def test6_Expected : Nat := 0

-- Test case 7: larger list, majority appears many times among diverse values
def test7_xs : List Nat := [7, 3, 7, 7, 2, 7, 1, 7, 7]
def test7_Expected : Nat := 7

-- Test case 8: majority appears exactly (floor(n/2)+1) times when n is odd
def test8_xs : List Nat := [9, 8, 9, 7, 9]
def test8_Expected : Nat := 9
end TestCases
