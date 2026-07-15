import Mathlib.Tactic

namespace VerinaSpec


def reverse_precond (a : Array Int) : Prop :=
  True

def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr

def reverse_postcond (a : Array Int) (result: Array Int) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)

end VerinaSpec

namespace LLMSpec

-- No helper functions are required for this specification.

def precondition (a : Array Int) : Prop :=
  True

-- The postcondition is purely relational:
-- it characterizes the output by size preservation and index-wise reverse correspondence.
-- Note: we use Nat subtraction (a.size - 1 - i). When i < a.size, this denotes the
-- intended mirror index; Array indexing with `!` is total, so the property is decidable
-- and simple to state.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ (i : Nat), i < a.size → result[i]! = a[(a.size - 1 - i)]!

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) :
  VerinaSpec.reverse_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result: Array Int) :
  LLMSpec.precondition a →
  (VerinaSpec.reverse_postcond a result ↔ LLMSpec.postcondition a result) := by
  sorry

end Proof
