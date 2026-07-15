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
    ReplaceSeparatorsWithColon: Replace every space, comma, or dot in a string with a colon.
    Natural language breakdown:
    1. Input is a string s (a sequence of characters).
    2. Output is a string result.
    3. The output has exactly the same number of characters as the input.
    4. For each character position i in the input:
       - If s[i] is ' ' (space) or ',' (comma) or '.' (dot), then result[i] is ':' (colon).
       - Otherwise result[i] equals s[i].
    5. No other characters are changed.
    6. There are no preconditions; all input strings are valid.
-/

section Specs
-- Helper: identify the separator characters that must be replaced.

def isSepChar (c : Char) : Bool :=
  (c = ' ') || (c = ',') || (c = '.')

-- Helper: the output character corresponding to an input character.

def replaceSep (c : Char) : Char :=
  if isSepChar c then ':' else c

-- Preconditions

def precondition (s : String) : Prop :=
  True

-- Postconditions
-- We specify behavior over the underlying character lists (`data`) to avoid any ambiguity
-- about the relation between `String.length` and indexing.

def postcondition (s : String) (result : String) : Prop :=
  result.data.length = s.data.length ∧
  ∀ (i : Nat), i < s.data.length →
    result.data[i]! = replaceSep (s.data[i]!)
end Specs

section Impl
method ReplaceSeparatorsWithColon (s : String)
  return (result : String)
  require precondition s
  ensures postcondition s result
  do
  pure ""  -- placeholder body

end Impl

section TestCases
-- Test case 1: example
-- "a b,c." -> "a:b:c:"
def test1_s : String := "a b,c."
def test1_Expected : String := "a:b:c:"

-- Test case 2: empty string

def test2_s : String := ""
def test2_Expected : String := ""

-- Test case 3: no separators (unchanged)

def test3_s : String := "abcXYZ123"
def test3_Expected : String := "abcXYZ123"

-- Test case 4: only separators

def test4_s : String := " , .,.  "
def test4_Expected : String := "::::::::"

-- Test case 5: leading/trailing separators

def test5_s : String := " .hello,world. "
def test5_Expected : String := "::hello:world::"

-- Test case 6: consecutive separators

def test6_s : String := "a..b,,c  d"
def test6_Expected : String := "a::b::c::d"

-- Test case 7: newline and tab are not replaced

def test7_s : String := "a\n b\t,c."
def test7_Expected : String := "a\n:b\t:c:"

-- Test case 8: Unicode characters preserved, only separators replaced

def test8_s : String := "λ,μ. ν"
def test8_Expected : String := "λ:μ::ν"

-- Test case 9: single-character strings

def test9_s : String := "."
def test9_Expected : String := ":"

-- Recommend to validate: test1_s, test4_s, test8_s
end TestCases
