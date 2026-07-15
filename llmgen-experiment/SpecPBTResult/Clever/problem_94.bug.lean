import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_94

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def precondition (lst : List Nat) : Prop :=
  lst.any (fun num => Nat.Prime num)

instance instDecidablePrecond (lst : List Nat) : Decidable (precondition lst) := by
  unfold precondition
  infer_instance

def postcondition (lst : List Nat) (result : Nat) :=
  result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
      (∀ j, (j < lst.length ∧ Prime (lst.get! j)) → lst.get! i ≤ lst.get! j) ∧
      result = (Nat.digits 10 (lst.get! i)).sum

end Specs

section Impl

def implementation (lst: List Nat) : Nat :=
sorry

end Impl

section TestCases

def test1_lst : List Nat := [0, 3, 2, 1, 3, 5, 7, 4, 5, 5, 5, 2, 181, 32, 4, 32, 3, 2, 32, 324, 4, 3]
def test1_Expected : Nat := 10

def test2_lst : List Nat := [1, 0, 1, 8, 2, 4597, 2, 1, 3, 40, 1, 2, 1, 2, 4, 2, 5, 1]
def test2_Expected : Nat := 25

def test3_lst : List Nat := [1, 3, 1, 32, 5107, 34, 83278, 109, 163, 23, 2323, 32, 30, 1, 9, 3]
def test3_Expected : Nat := 13

def test4_lst : List Nat := [0, 724, 32, 71, 99, 32, 6, 0, 5, 91, 83, 0, 5, 6]
def test4_Expected : Nat := 11

def test5_lst : List Nat := [0, 81, 12, 3, 1, 21]
def test5_Expected : Nat := 3

def test6_lst : List Nat := [0, 8, 1, 2, 1, 7]
def test6_Expected : Nat := 7

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : Nat) :
  result ≠ test1_Expected →
  ¬ postcondition test1_lst result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  intros; expose_names

  -- plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })

def postcondition_test1 :
  postcondition test1_lst 2 := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  simp [test1_lst];
  use 2
  aesop
  sorry
  native_decide +revert
