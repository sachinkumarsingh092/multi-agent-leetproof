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
    ToUppercase: Convert a given string to uppercase.
    Natural language breakdown:
    1. The input is a string `s`.
    2. The output is a string `result`.
    3. The output contains the same number of characters as the input.
    4. For every valid character index `i`, the character at position `i` in `result` is obtained
       by applying `Char.toUpper` to the character at position `i` in `s`.
    5. `Char.toUpper` converts lowercase ASCII letters 'a'..'z' to their uppercase counterparts
       and leaves all other characters unchanged.
    6. There are no preconditions.
-/

section Specs
-- Helper predicate: pointwise uppercase mapping over the `data : List Char` view of strings.
-- We specify the transformation character-by-character (not as a particular algorithm).
-- We also explicitly require length preservation at the character-list level.

def pointwiseToUpperData (s : String) (t : String) : Prop :=
  t.data.length = s.data.length ∧
  ∀ (i : Nat), i < s.data.length → t.data[i]! = (s.data[i]!).toUpper

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  pointwiseToUpperData s result
end Specs

section Impl
method ToUppercase (s : String)
  return (result : String)
  require precondition s
  ensures postcondition s result
  do
  pure s  -- placeholder body only

end Impl

section TestCases
-- Test case 1: mixed lowercase and uppercase letters
-- "HelloWorld" -> "HELLOWORLD"
def test1_s : String := "HelloWorld"
def test1_Expected : String := "HELLOWORLD"

-- Test case 2: empty input

def test2_s : String := ""
def test2_Expected : String := ""

-- Test case 3: all lowercase

def test3_s : String := "orange"
def test3_Expected : String := "ORANGE"

-- Test case 4: already uppercase

def test4_s : String := "LEAN"
def test4_Expected : String := "LEAN"

-- Test case 5: letters mixed with digits (digits unchanged)

def test5_s : String := "abc123XYZ"
def test5_Expected : String := "ABC123XYZ"

-- Test case 6: punctuation and spaces (unchanged except lowercase letters)

def test6_s : String := "a-b c!"
def test6_Expected : String := "A-B C!"

-- Test case 7: newline and tab characters (unchanged)

def test7_s : String := "a\n\tZ"
def test7_Expected : String := "A\n\tZ"

-- Test case 8: includes non-ASCII characters and a lowercase ASCII letter

def test8_s : String := "∃a∀"
def test8_Expected : String := "∃A∀"

-- Test case 9: singleton boundary input

def test9_s : String := "z"
def test9_Expected : String := "Z"

-- Recommend to validate: test1_Expected, test2_Expected, test9_Expected
end TestCases
