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
    IsPalindrome: Check if a given string is a palindrome.
    Natural language breakdown:
    1. The input is a string `s`, i.e., a finite sequence of characters.
    2. The output is a boolean `result`.
    3. The string is a palindrome exactly when its character sequence equals its reverse.
    4. The function returns `true` exactly when `s` is a palindrome.
    5. The function returns `false` exactly when `s` is not a palindrome.
    6. The empty string is a palindrome.
    7. Any single-character string is a palindrome.
    8. Whitespace, punctuation, and casing are treated as ordinary characters (no normalization).
-/

section Specs
-- Helper predicate: a list of characters is a palindrome iff it equals its reverse.
-- We define the core notion on `List Char` and apply it to `s.data : List Char`.
def isPalindromeChars (cs : List Char) : Prop :=
  cs = cs.reverse

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ isPalindromeChars s.data) ∧
  (result = false ↔ ¬ isPalindromeChars s.data)
end Specs

section Impl
method IsPalindrome (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure false  -- placeholder body only

prove_correct IsPalindrome by sorry
end Impl

section TestCases
-- Test case 1: empty string (edge case)
def test1_s : String := ""
def test1_Expected : Bool := true

-- Test case 2: singleton string (edge case)
def test2_s : String := "a"
def test2_Expected : Bool := true

-- Test case 3: two equal characters
def test3_s : String := "aa"
def test3_Expected : Bool := true

-- Test case 4: two different characters
def test4_s : String := "ab"
def test4_Expected : Bool := false

-- Test case 5: odd-length palindrome
def test5_s : String := "racecar"
def test5_Expected : Bool := true

-- Test case 6: odd-length non-palindrome
def test6_s : String := "racecat"
def test6_Expected : Bool := false

-- Test case 7: even-length palindrome
def test7_s : String := "noon"
def test7_Expected : Bool := true

-- Test case 8: even-length non-palindrome
def test8_s : String := "abcd"
def test8_Expected : Bool := false

-- Test case 9: whitespace treated as an ordinary character
def test9_s : String := "a a"
def test9_Expected : Bool := true

-- Test case 10: punctuation treated as ordinary characters ("a, a" is not a palindrome)
def test10_s : String := "a, a"
def test10_Expected : Bool := false

-- Recommend to validate: empty/singleton handling, even/odd length symmetry, whitespace and punctuation treated literally
end TestCases
