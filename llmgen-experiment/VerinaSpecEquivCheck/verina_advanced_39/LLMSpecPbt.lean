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
    MaxElementOfList: return the maximum element of a non-empty list of natural numbers.

    Natural language breakdown:
    1. The input is a list of natural numbers.
    2. The list is required to be non-empty.
    3. The output is a natural number.
    4. The output must be an element of the input list.
    5. Every element of the input list must be less than or equal to the output.
    6. Because the output is an element of the list and is an upper bound of the list elements,
       the output is the (unique) maximum value occurring in the list.
-/

section Specs
-- A simple, property-based characterization of being a maximum element of a list.
-- We avoid defining a reference implementation; instead we specify membership and upper-bound.

def isMaxOfList (lst : List Nat) (m : Nat) : Prop :=
  m ∈ lst ∧ ∀ (x : Nat), x ∈ lst → x ≤ m

-- Precondition: the list is non-empty.
-- Using lst ≠ [] keeps the condition decidable and simple.
def precondition (lst : List Nat) : Prop :=
  lst ≠ []

-- Postcondition: result is a maximum element of the list.
def postcondition (lst : List Nat) (result : Nat) : Prop :=
  isMaxOfList lst result
end Specs

section Impl
method MaxElementOfList (lst : List Nat)
  return (result : Nat)
  require precondition lst
  ensures postcondition lst result
  do
  -- Placeholder body only; replaced by a real implementation later.
  pure 0

prove_correct MaxElementOfList by sorry
end Impl

section TestCases
-- Test case 1: typical mixed list (mirrors the standard List.max? documentation example)
def test1_lst : List Nat := [1, 4, 2, 10, 6]
def test1_Expected : Nat := 10

-- Test case 2: singleton list (edge case)
def test2_lst : List Nat := [7]
def test2_Expected : Nat := 7

-- Test case 3: includes 0 (required boundary value for Nat)
def test3_lst : List Nat := [0, 5, 3]
def test3_Expected : Nat := 5

-- Test case 4: includes 1 (required boundary value for Nat)
def test4_lst : List Nat := [1, 0]
def test4_Expected : Nat := 1

-- Test case 5: all equal elements (duplicates)
def test5_lst : List Nat := [4, 4, 4, 4]
def test5_Expected : Nat := 4

-- Test case 6: maximum occurs multiple times

def test6_lst : List Nat := [2, 9, 1, 9, 3]
def test6_Expected : Nat := 9

-- Test case 7: strictly descending order

def test7_lst : List Nat := [9, 8, 7, 6]
def test7_Expected : Nat := 9

-- Test case 8: larger values

def test8_lst : List Nat := [1000, 2, 999]
def test8_Expected : Nat := 1000
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Nat) :
  result ≠ test8_Expected →
  ¬ postcondition test8_lst result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
