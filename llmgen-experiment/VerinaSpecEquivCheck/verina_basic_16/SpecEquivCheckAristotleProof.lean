/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 52b16529-ed89-4d3f-a446-6489bf508d8c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) (oldChar : Char) (newChar : Char) : VerinaSpec.replaceChars_precond s oldChar newChar ↔ LLMSpec.precondition s.toList.toArray oldChar newChar

- theorem postcondition_equiv (s : String) (oldChar : Char) (newChar : Char) (result : String) : LLMSpec.precondition s.toList.toArray oldChar newChar →
  (VerinaSpec.replaceChars_postcond s oldChar newChar result ↔ LLMSpec.postcondition s.toList.toArray oldChar newChar result.toList.toArray)
-/

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

theorem precondition_equiv (s : String) (oldChar : Char) (newChar : Char) : VerinaSpec.replaceChars_precond s oldChar newChar ↔ LLMSpec.precondition s.toList.toArray oldChar newChar := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.replaceChars_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (oldChar : Char) (newChar : Char) (result : String) : LLMSpec.precondition s.toList.toArray oldChar newChar →
  (VerinaSpec.replaceChars_postcond s oldChar newChar result ↔ LLMSpec.postcondition s.toList.toArray oldChar newChar result.toList.toArray) := by
  -- The postcondition for the VerinaSpec is equivalent to the postcondition for the LLMSpec because the length of the string is the same as the size of the array.
  simp [VerinaSpec.replaceChars_postcond, LLMSpec.postcondition];
  -- The two postconditions are equivalent because they both check the same conditions on the length and the characters.
  simp [String.length] at *;
  grind +ring

end Proof