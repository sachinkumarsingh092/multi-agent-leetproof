/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1c57b0b3-c885-480f-95a6-ab33b4ac2bff

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.isCleanPalindrome_precond s ↔ LLMSpec.precondition s
-/

import Mathlib.Tactic


namespace VerinaSpec

def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []

def isCleanPalindrome_precond (s : String) : Prop :=
  True

def reverseList (xs : List Char) : List Char :=
  xs.reverse

def isCleanPalindrome_postcond (s : String) (result: Bool) : Prop :=
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)

end VerinaSpec

namespace LLMSpec

-- Normalize a string for palindrome checking:
-- 1) lower-case each character
-- 2) keep only alphabetic characters
-- This returns a List Char since palindrome is naturally expressed via reverse.
def normalizedChars (s : String) : List Char :=
  (s.toLower.toList).filter (fun c => c.isAlpha)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ normalizedChars s = (normalizedChars s).reverse)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.isCleanPalindrome_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.isCleanPalindrome_precond, LLMSpec.precondition]

/- Aristotle failed to find a proof. -/
/- Manually checked this problem. Should be equivalent. -/
theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.isCleanPalindrome_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
