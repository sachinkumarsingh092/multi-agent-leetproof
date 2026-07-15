import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    PalindromeAlnumIgnoreCase: Determine whether an input text is a palindrome when ignoring all non-alphanumeric characters and ignoring case.
    Natural language breakdown:
    1. The input is a String (a sequence of characters).
    2. All characters that are not alphanumeric (not ASCII letters and not ASCII digits) are ignored.
    3. All remaining characters are compared case-insensitively, modeled by converting them to lowercase.
    4. Let the normalized sequence be the list of remaining characters after filtering and lowercasing.
    5. The input is a palindrome exactly when the normalized sequence equals its reverse.
    6. The output is a Bool that is true iff the normalized sequence is a palindrome.
    7. Empty input, or input that normalizes to empty, is considered a palindrome.
-/

section Specs
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
end Specs

section Impl
method PalindromeAlnumIgnoreCase (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true

prove_correct PalindromeAlnumIgnoreCase by sorry
end Impl

section TestCases
-- Test case 1: example from the prompt
-- "A man, a plan, a canal: Panama" is a palindrome under normalization.
def test1_s : String := "A man, a plan, a canal: Panama"
def test1_Expected : Bool := true

-- Test case 2: empty input
-- Normalizes to empty, which is a palindrome.
def test2_s : String := ""
def test2_Expected : Bool := true

-- Test case 3: only non-alphanumeric characters
-- Ignored entirely, normalizes to empty.
def test3_s : String := ".,:;!?()[]{}"
def test3_Expected : Bool := true

-- Test case 4: single alphanumeric character
-- Always a palindrome.
def test4_s : String := "Z"
def test4_Expected : Bool := true

-- Test case 5: simple non-palindrome
-- "ab" is not a palindrome.
def test5_s : String := "ab"
def test5_Expected : Bool := false

-- Test case 6: palindrome with mixed case
-- "Aa" is a palindrome when ignoring case.
def test6_s : String := "Aa"
def test6_Expected : Bool := true

-- Test case 7: palindrome with digits and punctuation
-- "1a2,2A1" normalizes to "1a22a1" which is a palindrome.
def test7_s : String := "1a2,2A1"
def test7_Expected : Bool := true

-- Test case 8: contains letters and digits, not a palindrome
-- "0P" normalizes to "0p" which is not a palindrome.
def test8_s : String := "0P"
def test8_Expected : Bool := false

-- Test case 9: classic palindrome with punctuation and spaces
-- "No 'x' in Nixon" normalizes to "noxinnixon" which is a palindrome.
def test9_s : String := "No 'x' in Nixon"
def test9_Expected : Bool := true

-- Recommend to validate: empty string, only punctuation, mixed-case palindrome
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Bool) :
  result ≠ test9_Expected →
  ¬ postcondition test9_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
