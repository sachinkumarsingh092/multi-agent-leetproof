import Mathlib.Tactic

namespace VerinaSpec


def reverseString_precond (s : String) : Prop :=
  True

def reverseString_postcond (s : String) (result: String) : Prop :=
  result.length = s.length ∧ result.toList = s.toList.reverse

end VerinaSpec

namespace LLMSpec

-- We specify correctness using the list-of-characters view of strings.
-- Note: String.toList : String → List Char

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  let cs := s.toList
  let rs := result.toList
  rs.length = cs.length ∧
  ∀ (i : Nat), i < cs.length →
    rs[i]! = cs[cs.length - 1 - i]!

end LLMSpec

section Proof

theorem precondition_equiv (s : String) :
  VerinaSpec.reverseString_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result: String) :
  LLMSpec.precondition s →
  (VerinaSpec.reverseString_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
