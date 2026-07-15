import Mathlib.Tactic

namespace VerinaSpec


def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e

def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)

end VerinaSpec

namespace LLMSpec

-- `e` must occur in `a` at some in-bounds index.
def precondition (a : Array Int) (e : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = e

-- `result` is an in-bounds index of the first occurrence of `e`.
def postcondition (a : Array Int) (e : Int) (result : Nat) : Prop :=
  result < a.size ∧
  a[result]! = e ∧
  (∀ j : Nat, j < a.size → j < result → a[j]! ≠ e)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (e : Int) :
  VerinaSpec.LinearSearch_precond a e ↔ LLMSpec.precondition a e := by
  sorry

theorem postcondition_equiv (a : Array Int) (e : Int) (result: Nat) :
  LLMSpec.precondition a e →
  (VerinaSpec.LinearSearch_postcond a e result ↔ LLMSpec.postcondition a e result) := by
  sorry

end Proof
