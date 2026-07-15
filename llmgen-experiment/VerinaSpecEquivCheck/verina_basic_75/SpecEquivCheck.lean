import Mathlib.Tactic

namespace VerinaSpec


def minArray_precond (a : Array Int) : Prop :=
  a.size > 0

def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin

def minArray_postcond (a : Array Int) (result: Int) :=
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)

end VerinaSpec

namespace LLMSpec

-- Precondition: the array is non-empty.
-- We keep this decidable/computable by using `a.size > 0`.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postcondition: `result` is a minimum element of `a`.
-- 1) Lower bound: result ≤ every element in the array.
-- 2) Attainment: result equals some element in the array.
def postcondition (a : Array Int) (result : Int) : Prop :=
  (∀ (i : Nat), i < a.size → result ≤ a[i]!) ∧
  (∃ (i : Nat), i < a.size ∧ result = a[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) :
  VerinaSpec.minArray_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result: Int) :
  LLMSpec.precondition a →
  (VerinaSpec.minArray_postcond a result ↔ LLMSpec.postcondition a result) := by
  sorry

end Proof
