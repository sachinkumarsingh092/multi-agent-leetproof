import Mathlib.Tactic

namespace VerinaSpec


def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  True

def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) :=
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))

end VerinaSpec

namespace LLMSpec

-- We use Mathlib/Lean's propositional prefix relation `p <+: s`.
-- `p <+: s` means: there exists some suffix t such that p ++ t = s.

-- No input restrictions.
def precondition (str1 : List Char) (str2 : List Char) : Prop :=
  True

-- Postcondition: `result` is a common prefix and is longest by length.
def postcondition (str1 : List Char) (str2 : List Char) (result : List Char) : Prop :=
  (result <+: str1) ∧
  (result <+: str2) ∧
  (∀ (p : List Char), (p <+: str1) → (p <+: str2) → p.length ≤ result.length)

end LLMSpec

section Proof

theorem precondition_equiv (str1 : List Char) (str2 : List Char) :
  VerinaSpec.LongestCommonPrefix_precond str1 str2 ↔ LLMSpec.precondition str1 str2 := by
  sorry

theorem postcondition_equiv (str1 : List Char) (str2 : List Char) (result: List Char) :
  LLMSpec.precondition str1 str2 →
  (VerinaSpec.LongestCommonPrefix_postcond str1 str2 result ↔ LLMSpec.postcondition str1 str2 result) := by
  sorry

end Proof
