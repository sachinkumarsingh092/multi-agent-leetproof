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
    ContainsAllVowels: Determine whether an input text contains all five English vowels.
    Natural language breakdown:
    1. The input is a string consisting only of alphabetic characters.
    2. The check is case-insensitive: uppercase letters count the same as their lowercase form.
    3. The five required vowels are the English vowels: 'a', 'e', 'i', 'o', 'u'.
    4. The output is a boolean.
    5. The result is true exactly when each of the five vowels occurs at least once in the input (ignoring case).
    6. If at least one required vowel does not occur, the result is false.
    7. The order and multiplicity of characters in the string do not matter beyond whether each vowel occurs.
-/

section Specs
-- We use a List of chars for the required vowels.
-- These are lowercase because we normalize the input via `String.toLower`.
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']

-- Lowercased character stream of the input.
def lowerChars (s : String) : List Char :=
  s.toLower.data

-- Predicate: the input contains all 5 vowels, case-insensitively.
def containsAllVowels (s : String) : Prop :=
  ∀ (v : Char), v ∈ vowels → v ∈ lowerChars s

def precondition (s : String) : Prop :=
  -- Problem statement restricts characters to alphabetic.
  ∀ (c : Char), c ∈ s.data → c.isAlpha = true

def postcondition (s : String) (result : Bool) : Prop :=
  -- Result is true iff all vowels occur at least once (case-insensitively).
  (result = true ↔ containsAllVowels s)
end Specs

section Impl
method ContainsAllVowels (s : String)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
    pure false

end Impl

section TestCases
-- Test case 1: all vowels present (simple lowercase)
def test1_s : String := "aeiou"
def test1_Expected : Bool := true

-- Test case 2: empty input (edge case)
def test2_s : String := ""
def test2_Expected : Bool := false

-- Test case 3: singleton input (edge case)
def test3_s : String := "a"
def test3_Expected : Bool := false

-- Test case 4: mixed case with all vowels present among consonants
def test4_s : String := "AbcDeIxOfU"
def test4_Expected : Bool := true

-- Test case 5: missing 'u'
def test5_s : String := "aeio"
def test5_Expected : Bool := false

-- Test case 6: uppercase vowels only
def test6_s : String := "AEIOU"
def test6_Expected : Bool := true

-- Test case 7: vowels spread out with many consonants
def test7_s : String := "qwertyasdfghijklopu"
def test7_Expected : Bool := true

-- Test case 8: missing vowel 'i'
def test8_s : String := "aeoub"
def test8_Expected : Bool := false

-- Test case 9: all vowels present in reverse order
def test9_s : String := "uoiea"
def test9_Expected : Bool := true

-- Recommend to validate: empty input behavior, case-insensitive matching, missing-vowel cases
end TestCases
