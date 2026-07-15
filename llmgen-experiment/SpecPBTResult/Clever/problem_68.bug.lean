import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_68

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]! % 2 = 0 ∧
  result[0]! = numbers[i]! ∧
  result[1]! = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

def precondition (numbers : List Nat) : Prop :=
  True

instance instDecidablePrecond (numbers : List Nat) : Decidable (precondition numbers) := by
  unfold precondition
  infer_instance

def postcondition (numbers : List Nat) (result : List Nat) :=
  (result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
  (result.length = 2 ↔ ∃ i, i < numbers.length ∧
    numbers[i]! % 2 = 0 ∧
    result[0]! = numbers[i]! ∧
    result[1]! = i ∧
    (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
    (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!))

end Specs

section Impl

def implementation (numbers: List Nat) : List Nat :=
sorry

end Impl

section TestCases

def test1_numbers : List Nat := [4, 2, 3]
def test1_Expected : List Nat := [2, 1]

def test2_numbers : List Nat := [1, 2, 3]
def test2_Expected : List Nat := [2, 1]

def test3_numbers : List Nat := []
def test3_Expected : List Nat := []

def test4_numbers : List Nat := [5, 0, 3, 0, 4, 2]
def test4_Expected : List Nat := [0, 1]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1 (result : List Nat) :
  result ≠ test1_Expected →
  ¬ postcondition test1_numbers result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
