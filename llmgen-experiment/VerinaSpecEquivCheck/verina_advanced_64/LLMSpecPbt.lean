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
    RemoveAllOccurrences: Remove all occurrences of a target natural number from a list.

    Natural language breakdown:
    1. Inputs are a list of natural numbers `lst` and a natural number `target`.
    2. The output is a list of natural numbers `result`.
    3. `result` is obtained by deleting every element of `lst` that is equal to `target`.
    4. No element equal to `target` appears in `result`.
    5. For every value `x` different from `target`, the number of occurrences of `x` is preserved.
    6. The relative order of the remaining elements is preserved (so `result` is an order-preserving
       subsequence of `lst`).
    7. The operation is total: it is defined for all `lst` and `target`.
-/

section Specs
-- Helper-free specification:
-- We use `List.Sublist` to express order-preserving subsequence and `List.count`
-- to express multiplicity preservation.

def precondition (lst : List Nat) (target : Nat) : Prop :=
  True

def postcondition (lst : List Nat) (target : Nat) (result : List Nat) : Prop :=
  result.Sublist lst ∧
  result.count target = 0 ∧
  (∀ x : Nat, x ≠ target → result.count x = lst.count x)
end Specs

section Impl
method RemoveAllOccurrences (lst : List Nat) (target : Nat)
  return (result : List Nat)
  require precondition lst target
  ensures postcondition lst target result
  do
  pure ([] : List Nat)  -- placeholder body only

prove_correct RemoveAllOccurrences by sorry
end Impl

section TestCases
-- Test case 1: empty list (degenerate input)
def test1_lst : List Nat := []
def test1_target : Nat := 0
def test1_Expected : List Nat := []

-- Test case 2: singleton list equal to target

def test2_lst : List Nat := [1]
def test2_target : Nat := 1
def test2_Expected : List Nat := []

-- Test case 3: singleton list not equal to target

def test3_lst : List Nat := [1]
def test3_target : Nat := 0
def test3_Expected : List Nat := [1]

-- Test case 4: list with no occurrences of target

def test4_lst : List Nat := [2, 3, 4]
def test4_target : Nat := 1
def test4_Expected : List Nat := [2, 3, 4]

-- Test case 5: list with all occurrences equal to target

def test5_lst : List Nat := [0, 0, 0]
def test5_target : Nat := 0
def test5_Expected : List Nat := []

-- Test case 6: mixed list, remove repeated target values

def test6_lst : List Nat := [3, 1, 3, 2, 3, 4]
def test6_target : Nat := 3
def test6_Expected : List Nat := [1, 2, 4]

-- Test case 7: target at head and tail

def test7_lst : List Nat := [5, 1, 2, 5]
def test7_target : Nat := 5
def test7_Expected : List Nat := [1, 2]

-- Test case 8: alternating target/non-target

def test8_lst : List Nat := [0, 1, 0, 1, 0, 1]
def test8_target : Nat := 0
def test8_Expected : List Nat := [1, 1, 1]

-- Test case 9: repeated non-target values preserved (multiplicity)

def test9_lst : List Nat := [2, 2, 1, 2, 1, 2]
def test9_target : Nat := 1
def test9_Expected : List Nat := [2, 2, 2, 2]

-- Recommend to validate: test1_Expected, test6_Expected, test9_Expected
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : List Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_lst test9_target result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
