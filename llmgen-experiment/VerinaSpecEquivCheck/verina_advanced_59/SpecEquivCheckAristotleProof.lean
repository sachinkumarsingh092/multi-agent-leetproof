/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 00cf3854-34aa-41e7-8c9d-ca405e20f8f4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.palindromeIgnoreNonAlnum_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.palindromeIgnoreNonAlnum_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  True

def palindromeIgnoreNonAlnum_postcond (s : String) (result: Bool) : Prop :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
let forward := cleaned
let backward := cleaned.reverse
if result then
  forward = backward
else
  forward ≠ backward

end VerinaSpec

namespace LLMSpec

-- Helper: normalize a string into the sequence actually compared.
-- We keep only alphanumeric characters and lowercase them.
-- We use List Char for specifications to avoid Array/List mixing.
def normalizeAlnumLower (s : String) : List Char :=
  (s.toList.filter Char.isAlphanum).map Char.toLower

-- Helper: palindrome predicate on the normalized sequence.
def isNormalizedPalindrome (s : String) : Prop :=
  let t : List Char := normalizeAlnumLower s
  t.reverse = t

-- No preconditions: all strings are allowed.
def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ isNormalizedPalindrome s)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.palindromeIgnoreNonAlnum_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.palindromeIgnoreNonAlnum_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s →
  (VerinaSpec.palindromeIgnoreNonAlnum_postcond s result ↔ LLMSpec.postcondition s result) := by
  unfold VerinaSpec.palindromeIgnoreNonAlnum_postcond LLMSpec.postcondition;
  -- By definition of `normalizeAlnumLower`, we know that `cleaned` is equal to `normalizeAlnumLower s`.
  have h_cleaned : List.map Char.toLower (List.filter (fun c => c.isAlpha || c.isDigit) s.data) = LLMSpec.normalizeAlnumLower s := by
    congr! 2;
  -- By definition of `isNormalizedPalindrome`, we know that `t.reverse = t` if and only if `t` is a palindrome.
  have h_palindrome : LLMSpec.isNormalizedPalindrome s ↔ (LLMSpec.normalizeAlnumLower s).reverse = LLMSpec.normalizeAlnumLower s := by
    exact?;
  grind +ring

end Proof