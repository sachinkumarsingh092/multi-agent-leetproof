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
    ToLowercase: Convert all uppercase characters in a string to their lowercase equivalents.
    Natural language breakdown:
    1. The input is a string (a finite sequence of characters).
    2. For each position in the string, if the input character is an uppercase ASCII letter, the output character is its lowercase form.
    3. For each position in the string, if the input character is not an uppercase ASCII letter, the output character is unchanged.
    4. The output string has exactly the same length as the input string.
    5. The transformation is pointwise: each output character depends only on the corresponding input character.
    6. There are no preconditions; the method must accept any string.
-/

section Specs
-- Helper: the intended per-character transformation.
-- `Char.toLower` converts uppercase ASCII letters to their lowercase counterpart, and leaves other characters unchanged.
def lowerChar (c : Char) : Char :=
  c.toLower

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  let sl := s.toList
  let rl := result.toList
  rl.length = sl.length ∧
  ∀ (i : Nat), i < sl.length → rl[i]! = lowerChar (sl[i]!)
end Specs

section Impl
method ToLowercase (s : String)
  return (result : String)
  require precondition s
  ensures postcondition s result
  do
  pure s  -- placeholder body only

prove_correct ToLowercase by sorry
end Impl

section TestCases
-- Test case 1: mixed ASCII letters
-- Example: "AbCz" -> "abcz"
def test1_s : String := "AbCz"
def test1_Expected : String := "abcz"

-- Test case 2: empty string
def test2_s : String := ""
def test2_Expected : String := ""

-- Test case 3: singleton uppercase
def test3_s : String := "Z"
def test3_Expected : String := "z"

-- Test case 4: singleton lowercase (unchanged)
def test4_s : String := "m"
def test4_Expected : String := "m"

-- Test case 5: all lowercase (unchanged)
def test5_s : String := "hello"
def test5_Expected : String := "hello"

-- Test case 6: all uppercase
def test6_s : String := "ABCDEF"
def test6_Expected : String := "abcdef"

-- Test case 7: digits and punctuation (unchanged)
def test7_s : String := "123!?"
def test7_Expected : String := "123!?"

-- Test case 8: includes whitespace and newline
def test8_s : String := "\nX y"
def test8_Expected : String := "\nx y"

-- Test case 9: mixed content with underscores and capitalization
def test9_s : String := "Lean_4_Is_FUN"
def test9_Expected : String := "lean_4_is_fun"

-- Recommend to validate: test1_s, test6_s, test8_s
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : String) :
  result ≠ test8_Expected →
  ¬ postcondition test8_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
