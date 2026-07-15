import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    PalindromeCheck: Determine whether a string is a palindrome when ignoring non-alphabetic characters
    Natural language breakdown:
    1. Input is a string s.
    2. We normalize s by (a) converting all characters to lowercase and (b) removing all non-alphabetic characters.
    3. The output is a boolean result.
    4. The result is true exactly when the normalized sequence of characters reads the same forwards and backwards.
    5. Whitespace, punctuation, digits, and any other non-alphabetic characters are ignored.
    6. Capitalization is ignored.
-/

section Specs
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
end Specs

section Impl
method PalindromeCheck (s : String) return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
    pure false  -- placeholder body

prove_correct PalindromeCheck by sorry
end Impl

section TestCases
-- Test case 1: empty string (degenerate case)
def test1_s : String := ""
def test1_Expected : Bool := true

-- Test case 2: single alphabetic character
def test2_s : String := "x"
def test2_Expected : Bool := true

-- Test case 3: simple even-length palindrome
def test3_s : String := "aa"
def test3_Expected : Bool := true

-- Test case 4: simple non-palindrome
def test4_s : String := "ab"
def test4_Expected : Bool := false

-- Test case 5: case-insensitive palindrome
def test5_s : String := "Aba"
def test5_Expected : Bool := true

-- Test case 6: ignore punctuation and spaces (classic palindrome phrase)
def test6_s : String := "A man, a plan, a canal: Panama"
def test6_Expected : Bool := true

-- Test case 7: ignore punctuation and spaces (another phrase)
def test7_s : String := "No lemon, no melon"
def test7_Expected : Bool := true

-- Test case 8: digits and symbols are ignored; remaining letters form a palindrome
def test8_s : String := "0P!"
def test8_Expected : Bool := true

-- Test case 9: mixed characters, not a palindrome after normalization
def test9_s : String := "Hello, World!"
def test9_Expected : Bool := false
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
