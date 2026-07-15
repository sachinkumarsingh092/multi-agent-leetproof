/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9a9646ad-439c-4980-8298-f649a41294c8

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.isPalindrome_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.isPalindrome_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isPalindrome_precond (s : String) : Prop :=
  True

def isPalindrome_postcond (s : String) (result: Bool) : Prop :=
  (result → (s.toList == s.toList.reverse)) ∧
  (¬ result → (s.toList ≠ [] ∧ s.toList != s.toList.reverse))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: a list of characters is a palindrome iff it equals its reverse.
-- We define the core notion on `List Char` and apply it to `s.data : List Char`.
def isPalindromeChars (cs : List Char) : Prop :=
  cs = cs.reverse

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ isPalindromeChars s.data) ∧
  (result = false ↔ ¬ isPalindromeChars s.data)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.isPalindrome_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, the equivalence is trivially true.
  simp [VerinaSpec.isPalindrome_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.isPalindrome_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- By definition of `isPalindromePostcond`, we know that `s` is a palindrome if and only if `s.toList` is equal to its reverse. Therefore, the postconditions are equivalent.
  simp [VerinaSpec.isPalindrome_postcond, LLMSpec.postcondition, LLMSpec.isPalindromeChars];
  grind

end Proof