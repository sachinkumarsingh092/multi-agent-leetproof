import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_96

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : List Nat) :=
  match n with
  | 0 => result = []
  | n => n > 0 → (∀ i, i < result.length → (Nat.Prime (result.get! i)) ∧ (result.get! i) < n) ∧
         (∀ i : Nat, i < n → Nat.Prime i → i ∈ result)
-- program termination
∃ result,
  implementation n = result ∧
  spec result

def precondition (n : Nat) : Prop :=
  True

instance instDecidablePrecond (n : Nat) : Decidable (precondition n) := by
  unfold precondition
  infer_instance

def postcondition (n : Nat) (result : List Nat) :=
  match n with
    | 0 => result = []
    | n => n > 0 →
    (∀ i, i < result.length → (Nat.Prime (result.get! i)) ∧ (result.get! i) < n) ∧
           (∀ i : Nat, i < n → Nat.Prime i → i ∈ result)

end Specs

section Impl

def implementation (n: Nat) : List Nat :=
sorry

end Impl

section TestCases

def test1_n : Nat := 5
def test1_Expected : List Nat := [2, 3]

def test2_n : Nat := 11
def test2_Expected : List Nat := [2, 3, 5, 7]

def test3_n : Nat := 0
def test3_Expected : List Nat := []

def test4_n : Nat := 20
def test4_Expected : List Nat := [2, 3, 5, 7, 11, 13, 17, 19]

def test5_n : Nat := 1
def test5_Expected : List Nat := []

def test6_n : Nat := 18
def test6_Expected : List Nat := [2, 3, 5, 7, 11, 13, 17]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1' (result : List Nat) :
  result ≠ test1_Expected →
  ¬ postcondition test1_n result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
