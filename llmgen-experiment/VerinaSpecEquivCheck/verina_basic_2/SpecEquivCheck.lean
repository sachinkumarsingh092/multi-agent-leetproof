import Mathlib.Tactic

namespace VerinaSpec


def findSmallest_precond (s : Array Nat) : Prop :=
  True

def findSmallest_postcond (s : Array Nat) (result: Option Nat) :=
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)

end VerinaSpec

namespace LLMSpec

def precondition (s : Array Nat) : Prop :=
  True

def postcondition (s : Array Nat) (result : Option Nat) : Prop :=
  match result with
  | none => s.size = 0
  | some m =>
      s.size > 0 ∧ m ∈ s ∧ ∀ x : Nat, x ∈ s → m ≤ x

end LLMSpec

section Proof

theorem precondition_equiv (s : Array Nat) :
  VerinaSpec.findSmallest_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : Array Nat) (result: Option Nat) :
  LLMSpec.precondition s →
  (VerinaSpec.findSmallest_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
