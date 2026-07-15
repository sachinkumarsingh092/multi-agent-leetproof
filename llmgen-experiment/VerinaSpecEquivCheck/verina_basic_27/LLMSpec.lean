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
    FirstRepeatedChar: identify the first repeated character in a given string.
    Natural language breakdown:
    1. The input is a string s, which is a finite sequence of characters.
    2. An occurrence at index j is a repeated occurrence if the same character occurred at some earlier index i < j.
    3. The first repeated character is the character at the smallest index j that is a repeated occurrence.
    4. If such an index exists, the result is `some c` where c is that first repeated character.
    5. If no such index exists (all characters are unique), the result is `none`.
    6. There are no preconditions; the method must behave correctly for empty and non-empty strings.
-/

section Specs
-- We reason about a `String` via its underlying list of characters.
-- This is a definitional projection in Lean (`String.data : List Char`).
def chars (s : String) : List Char :=
  s.data

-- Predicate: index j (in the character list) is a repeated occurrence.
def isRepeatIndex (s : String) (j : Nat) : Prop :=
  j < (chars s).length ∧
  ∃ i : Nat, i < j ∧ (chars s)[i]! = (chars s)[j]!

-- Predicate: j is the first index (left-to-right) at which a repeat occurs.
def isFirstRepeatIndex (s : String) (j : Nat) : Prop :=
  isRepeatIndex s j ∧
  ∀ k : Nat, k < j → ¬ isRepeatIndex s k

-- No preconditions.
def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Option Char) : Prop :=
  -- `none` exactly when there is no repeated index
  (result = none ↔ (∀ j : Nat, j < (chars s).length → ¬ isRepeatIndex s j)) ∧
  -- if `some c`, then c is the character at some first-repeat index
  (∀ c : Char, result = some c → (∃ j : Nat, isFirstRepeatIndex s j ∧ (chars s)[j]! = c)) ∧
  -- uniqueness: any first-repeat index must have the returned character
  (∀ c : Char, result = some c → (∀ j : Nat, isFirstRepeatIndex s j → (chars s)[j]! = c))
end Specs

section Impl
method FirstRepeatedChar (s : String)
  return (result : Option Char)
  require precondition s
  ensures postcondition s result
  do
  pure none  -- placeholder

end Impl

section TestCases
-- Test case 1: typical repetition later
-- s = "abca" -> first repeated is 'a'
def test1_s : String := "abca"
def test1_Expected : Option Char := some 'a'

-- Test case 2: immediate repetition
-- s = "aab" -> first repeated is 'a'
def test2_s : String := "aab"
def test2_Expected : Option Char := some 'a'

-- Test case 3: first repeat is not the lexicographically smallest character
-- s = "abba" -> first repeated is 'b' (repeat at index 2)
def test3_s : String := "abba"
def test3_Expected : Option Char := some 'b'

-- Test case 4: no repetition
-- s = "abc" -> none
def test4_s : String := "abc"
def test4_Expected : Option Char := none

-- Test case 5: empty string
-- s = "" -> none
def test5_s : String := ""
def test5_Expected : Option Char := none

-- Test case 6: singleton
-- s = "z" -> none
def test6_s : String := "z"
def test6_Expected : Option Char := none

-- Test case 7: multiple repeats; ensure first repeated occurrence determines answer
-- s = "abcbad" -> first repeated is 'b' (repeat at index 3)
def test7_s : String := "abcbad"
def test7_Expected : Option Char := some 'b'

-- Test case 8: all characters identical
-- s = "xxx" -> first repeated is 'x'
def test8_s : String := "xxx"
def test8_Expected : Option Char := some 'x'

-- Test case 9: includes control characters
-- s = "\n\t\n" -> first repeated is '\n'
def test9_s : String := "\n\t\n"
def test9_Expected : Option Char := some '\n'

-- Recommend to validate: empty input, all-unique input, multiple repeats
end TestCases
