/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d70dc22e-8381-4e50-867d-b62421b45010

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.containsZ_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.containsZ_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def containsZ_precond (s : String) : Prop :=
  True

def containsZ_postcond (s : String) (result: Bool) :=
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result

end VerinaSpec

namespace LLMSpec

-- Helper: view a string as the list of its characters.
-- Note: we keep the method interface as String to match the problem statement.
def toChars (s : String) : List Char :=
  s.data

def hasZ (s : String) : Prop :=
  ('z' ∈ toChars s) ∨ ('Z' ∈ toChars s)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ hasZ s)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.containsZ_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.containsZ_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.containsZ_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- By definition of `postcondition`, we know that `result = true` if and only if `hasZ s`.
  simp [LLMSpec.postcondition, LLMSpec.hasZ];
  -- By definition of `postcondition`, we know that `result = true` if and only if `hasZ s`. Therefore, the equivalence holds.
  simp [VerinaSpec.containsZ_postcond, LLMSpec.toChars];
  grind

end Proof