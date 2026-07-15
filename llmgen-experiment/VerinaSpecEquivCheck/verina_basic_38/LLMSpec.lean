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
    AllCharsIdentical: Check whether all characters in an input string are identical.
    Natural language breakdown:
    1. The input is a string `s`, i.e., a finite sequence of characters.
    2. The output is a Boolean value.
    3. The output is true exactly when every character occurring in the string is equal to every other character.
    4. The empty string is considered to have all characters identical, so the output is true.
    5. A single-character string is considered to have all characters identical, so the output is true.
    6. If there exists at least one character in the string that differs from another, the output is false.
-/

section Specs
-- Helper predicate: all characters of a list are identical.
-- This is formulated without committing to any particular algorithm:
-- either the list is empty, or all elements in the tail equal the head.
-- (For a singleton list, the tail is empty, so the condition holds.)
def allCharsIdenticalList (lst : List Char) : Prop :=
  match lst with
  | [] => True
  | c :: cs => ∀ (d : Char), d ∈ cs → d = c

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Bool) : Prop :=
  (result = true ↔ allCharsIdenticalList s.data)
end Specs

section Impl
method AllCharsIdentical (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  pure true

end Impl

section TestCases
-- Test case 1: empty string (edge case: vacuously all identical)
def test1_s : String := ""
def test1_Expected : Bool := true

-- Test case 2: singleton string (edge case)
def test2_s : String := "a"
def test2_Expected : Bool := true

-- Test case 3: all characters the same
def test3_s : String := "xxxx"
def test3_Expected : Bool := true

-- Test case 4: differing last character
def test4_s : String := "xxxy"
def test4_Expected : Bool := false

-- Test case 5: alternating characters
def test5_s : String := "abab"
def test5_Expected : Bool := false

-- Test case 6: two-character equal
def test6_s : String := "bb"
def test6_Expected : Bool := true

-- Test case 7: two-character different
def test7_s : String := "bc"
def test7_Expected : Bool := false

-- Test case 8: whitespace characters, all identical
def test8_s : String := "   "
def test8_Expected : Bool := true

-- Test case 9: includes newline characters, all identical
def test9_s : String := "\n\n\n"
def test9_Expected : Bool := true

-- Recommend to validate: empty/singleton handling, differing-at-end, non-alphanumeric characters
end TestCases
