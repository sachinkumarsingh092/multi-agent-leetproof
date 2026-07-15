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

theorem precondition_equiv (s : String) :
  VerinaSpec.isCleanPalindrome_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result: Bool) :
  LLMSpec.precondition s →
  (VerinaSpec.isCleanPalindrome_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
