import Mathlib.Tactic

namespace VerinaSpec


def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True

def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))

end VerinaSpec

namespace LLMSpec

-- We model strings as `Array Char` (instead of `String`) to avoid `String` in specifications.

def precondition (s : Array Char) (oldChar : Char) (newChar : Char) : Prop :=
  True

def postcondition (s : Array Char) (oldChar : Char) (newChar : Char) (result : Array Char) : Prop :=
  result.size = s.size ∧
  (∀ (i : Nat), i < s.size →
    result[i]! = (if s[i]! = oldChar then newChar else s[i]!))

end LLMSpec

section Proof

theorem precondition_equiv (s : String) (oldChar : Char) (newChar : Char) :
  VerinaSpec.replaceChars_precond s oldChar newChar ↔ LLMSpec.precondition s.toList.toArray oldChar newChar := by
  sorry

theorem postcondition_equiv (s : String) (oldChar : Char) (newChar : Char) (result: String) :
  LLMSpec.precondition s.toList.toArray oldChar newChar →
  (VerinaSpec.replaceChars_postcond s oldChar newChar result ↔ LLMSpec.postcondition s.toList.toArray oldChar newChar result.toList.toArray) := by
  sorry

end Proof
