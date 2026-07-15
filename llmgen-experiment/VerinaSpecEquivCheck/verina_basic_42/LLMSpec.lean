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
    CountDigitsInString: count the number of digit characters in an input string.
    Natural language breakdown:
    1. Input is a string s.
    2. A character is considered a digit exactly when it is an ASCII digit between '0' and '9'.
    3. The output is a natural number giving how many characters of s are digits.
    4. The method must work for all strings; there are no input restrictions.
-/

section Specs
-- Helper: reuse the standard digit predicate on characters.
def isDigitChar (c : Char) : Bool :=
  c.isDigit

-- We count digits in the character list of the string.
def digitCount (s : String) : Nat :=
  s.toList.countP (fun c => isDigitChar c)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Nat) : Prop :=
  result = digitCount s
end Specs

section Impl
method CountDigitsInString (s : String)
  return (result : Nat)
  require precondition s
  ensures postcondition s result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: empty string
-- Expected: 0

def test1_s : String := ""

def test1_Expected : Nat := 0

-- Test case 2: single digit

def test2_s : String := "0"

def test2_Expected : Nat := 1

-- Test case 3: single non-digit

def test3_s : String := "a"

def test3_Expected : Nat := 0

-- Test case 4: all digits

def test4_s : String := "12345"

def test4_Expected : Nat := 5

-- Test case 5: no digits

def test5_s : String := "abcXYZ"

def test5_Expected : Nat := 0

-- Test case 6: mixed alphanumerics

def test6_s : String := "a1b2c3"

def test6_Expected : Nat := 3

-- Test case 7: digits with punctuation and spaces

def test7_s : String := " 9-8+7 "

def test7_Expected : Nat := 3

-- Test case 8: leading zeros and letters

def test8_s : String := "00a00"

def test8_Expected : Nat := 4

-- Test case 9: non-ASCII digit character should not count as an ASCII digit
-- Arabic-Indic digit nine U+0669

def test9_s : String := "x٩y"

def test9_Expected : Nat := 0
end TestCases
