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
    ReverseString: Reverse the characters of an input string.
    Natural language breakdown:
    1. The input is a string s, which may be empty.
    2. The output is a string result.
    3. The output contains exactly the same characters as s, but in reverse order.
    4. The length of result equals the length of s.
    5. For every valid index i into s (0-based), the character at position i in result
       equals the character at position (len-1-i) in s, where len is the number of characters.
-/

section Specs
-- We specify correctness using the list-of-characters view of strings.
-- Note: String.toList : String → List Char

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  let cs := s.toList
  let rs := result.toList
  rs.length = cs.length ∧
  ∀ (i : Nat), i < cs.length →
    rs[i]! = cs[cs.length - 1 - i]!
end Specs

section Impl
method ReverseString (s : String)
  return (result : String)
  require precondition s
  ensures postcondition s result
  do
    pure ""  -- placeholder body

end Impl

section TestCases
-- Test case 1: typical ASCII
def test1_s : String := "abc"
def test1_Expected : String := "cba"

-- Test case 2: empty string
def test2_s : String := ""
def test2_Expected : String := ""

-- Test case 3: single character
def test3_s : String := "x"
def test3_Expected : String := "x"

-- Test case 4: palindrome
def test4_s : String := "racecar"
def test4_Expected : String := "racecar"

-- Test case 5: with spaces
def test5_s : String := "a b"
def test5_Expected : String := "b a"

-- Test case 6: repeated characters
def test6_s : String := "aaaa"
def test6_Expected : String := "aaaa"

-- Test case 7: includes punctuation
def test7_s : String := "ab!c?"
def test7_Expected : String := "?c!ba"

-- Test case 8: includes unicode characters
def test8_s : String := "L∃∀N"
def test8_Expected : String := "N∀∃L"

-- Test case 9: includes newline
def test9_s : String := "a\n"
def test9_Expected : String := "\na"
end TestCases
