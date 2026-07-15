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
    verina_basic_33: Return the smallest natural number missing from a sorted list of natural numbers.
    Natural language breakdown:
    1. The input is a list s : List Nat.
    2. The list is assumed to be sorted in non-decreasing order.
    3. The output is a natural number result.
    4. result is the smallest natural number that does not occur in s.
    5. Equivalently: result is not a member of s, and every natural number smaller than result is a member of s.
-/

section Specs
-- A value is “missing” from the list if it is not a member.
-- “Smallest missing” is characterized by non-membership plus membership of all smaller naturals.

def precondition (s : List Nat) : Prop :=
  s.Sorted (· ≤ ·)

def postcondition (s : List Nat) (result : Nat) : Prop :=
  (result ∉ s) ∧
  (∀ (n : Nat), n < result → n ∈ s)
end Specs

section Impl
method smallestMissingNat (s : List Nat)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
    pure 0

prove_correct smallestMissingNat by sorry
end Impl

section TestCases
-- Test case 1: empty list; 0 is missing
def test1_s : List Nat := []
def test1_Expected : Nat := 0

-- Test case 2: singleton containing 0; next missing is 1
def test2_s : List Nat := [0]
def test2_Expected : Nat := 1

-- Test case 3: list does not contain 0; smallest missing is 0
def test3_s : List Nat := [1, 2, 3]
def test3_Expected : Nat := 0

-- Test case 4: typical gap in the middle
def test4_s : List Nat := [0, 1, 3, 4]
def test4_Expected : Nat := 2

-- Test case 5: duplicates are allowed; still find first missing
def test5_s : List Nat := [0, 0, 1, 2]
def test5_Expected : Nat := 3

-- Test case 6: duplicates and missing 1
def test6_s : List Nat := [0, 2, 2, 3]
def test6_Expected : Nat := 1

-- Test case 7: consecutive prefix starting at 0; missing is length
def test7_s : List Nat := [0, 1, 2, 3, 4]
def test7_Expected : Nat := 5

-- Test case 8: singleton not containing 0
def test8_s : List Nat := [2]
def test8_Expected : Nat := 0

-- Test case 9: large jump after a consecutive prefix
def test9_s : List Nat := [0, 1, 2, 100]
def test9_Expected : Nat := 3
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
