import Mathlib.Tactic

namespace VerinaSpec


def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) :=
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

end VerinaSpec

namespace LLMSpec

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size + b.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = a[i]!) ∧
  (∀ (j : Nat), j < b.size → result[a.size + j]! = b[j]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) :
  VerinaSpec.concat_precond a b ↔ LLMSpec.precondition a b := by
  sorry

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result: Array Int) :
  LLMSpec.precondition a b →
  (VerinaSpec.concat_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  sorry

end Proof
