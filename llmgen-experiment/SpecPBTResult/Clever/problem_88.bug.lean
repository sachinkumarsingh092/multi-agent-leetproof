import SpecPBTResult.Clever.CleverAllImports
import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: problem_88

section Specs

register_specdef_allow_recursion

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  lst.length > 0 →
  result.length = lst.length ∧
  (∀ i, i < result.length →
    result[i]! ∈ lst ∧
    lst[i]! ∈ result ∧
    result.count (lst[i]!) = lst.count (lst[i]!)) ∧
  (lst.head! + lst.getLast!) ≡ 1 [MOD 2] →
    result.Sorted Nat.le ∧
  (lst.head! + lst.getLast!) ≡ 0 [MOD 2] →
    result.Sorted (fun a b => a ≥ b)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def precondition (lst : List Nat) : Prop :=
  lst.length > 0

instance instDecidablePrecond (lst : List Nat) : Decidable (precondition lst) := by
  unfold precondition
  infer_instance

def postcondition (lst : List Nat) (result : List Nat) :=
  result.length = lst.length ∧
    (∀ i, i < result.length →
      result[i]! ∈ lst ∧
      lst[i]! ∈ result ∧
      result.count (lst[i]!) = lst.count (lst[i]!)) ∧
    (lst.head! + lst.getLast!) ≡ 1 [MOD 2] →
    result.Sorted Nat.le ∧
    (lst.head! + lst.getLast!) ≡ 0 [MOD 2] →
    result.Sorted (fun a b => a ≥ b)

end Specs

section Impl

def implementation (lst: List Nat) : List Nat :=
sorry

end Impl

section TestCases

def test1_lst : List Nat := []
def test1_Expected : List Nat := []

def test2_lst : List Nat := [5]
def test2_Expected : List Nat := [5]

def test3_lst : List Nat := [2, 4, 3, 0, 1, 5]
def test3_Expected : List Nat := [0, 1, 2, 3, 4, 5]

def test4_lst : List Nat := [2, 4, 3, 0, 1, 5, 6]
def test4_Expected : List Nat := [6, 5, 4, 3, 2, 1, 0]

end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1' (result : List Nat) :
  result ≠ test1_Expected →
  ¬ postcondition test1_lst result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 10000 })
