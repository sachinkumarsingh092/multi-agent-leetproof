/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c1f49205-23ef-4f96-986a-cec3cd755ce0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (str1 : List Char) (str2 : List Char) : VerinaSpec.LongestCommonPrefix_precond str1 str2 ↔ LLMSpec.precondition str1 str2

- theorem postcondition_equiv (str1 : List Char) (str2 : List Char) (result : List Char) : LLMSpec.precondition str1 str2 →
  (VerinaSpec.LongestCommonPrefix_postcond str1 str2 result ↔ LLMSpec.postcondition str1 str2 result)
-/

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

theorem precondition_equiv (str1 : List Char) (str2 : List Char) : VerinaSpec.LongestCommonPrefix_precond str1 str2 ↔ LLMSpec.precondition str1 str2 := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.LongestCommonPrefix_precond, LLMSpec.precondition]

theorem postcondition_equiv (str1 : List Char) (str2 : List Char) (result : List Char) : LLMSpec.precondition str1 str2 →
  (VerinaSpec.LongestCommonPrefix_postcond str1 str2 result ↔ LLMSpec.postcondition str1 str2 result) := by
  -- By definition of `postcondition`, the two postconditions are equivalent if the result is a common prefix and no longer prefix exists.
  simp [VerinaSpec.LongestCommonPrefix_postcond, LLMSpec.postcondition] at *;
  intro h;
  constructor <;> intro H' <;> rcases H' with ⟨ h₁, h₂, h₃ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · grind;
    · exact h₃.2.1.symm ▸ List.take_prefix _ _;
    · intro p hp₁ hp₂; rcases hp₁ with ⟨ q, rfl ⟩ ; rcases hp₂ with ⟨ r, hr ⟩ ; simp +decide [ List.take_take ] at *;
      grind +ring;
  · rcases h₁ with ⟨ t₁, rfl ⟩ ; rcases h₂ with ⟨ t₂, rfl ⟩ ; simp_all +decide [ List.take_append ] ;
    contrapose! h₃;
    rcases t₁ with ( _ | ⟨ a, t₁ ⟩ ) <;> rcases t₂ with ( _ | ⟨ b, t₂ ⟩ ) <;> simp_all +decide [ List.getElem?_append ];
    exact ⟨ result ++ [ b ], by simp +decide [ List.prefix_append ], by simp +decide [ List.prefix_append ], by simp +decide ⟩

end Proof