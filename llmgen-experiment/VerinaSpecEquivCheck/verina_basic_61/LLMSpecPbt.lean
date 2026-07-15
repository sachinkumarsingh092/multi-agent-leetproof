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
    AllCharsAreDigits: Determine whether every character in an input string is a digit.

    Natural language breakdown:
    1. The input is a finite sequence of characters.
    2. We model the string as an `Array Char` (project guideline: avoid `String` in signatures/specs).
    3. A character counts as a digit exactly when `Char.isDigit` returns true (ASCII '0'..'9').
    4. The output is a boolean value.
    5. The output is true iff every character in the input sequence is a digit.
    6. If the input is empty, the output is true (vacuously: there is no counterexample).
-/

section Specs
-- Helper predicate: every character in the array is an ASCII digit.
def allDigits (s : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → (s[i]!).isDigit = true

-- No preconditions.
def precondition (s : Array Char) : Prop :=
  True

def postcondition (s : Array Char) (result : Bool) : Prop :=
  (result = true ↔ allDigits s)
end Specs

section Impl
method AllCharsAreDigits (s : Array Char)
  return (result : Bool)
  require precondition s
  ensures postcondition s result
  do
  -- Placeholder body only (must typecheck).
  pure true

prove_correct AllCharsAreDigits by sorry
end Impl

section TestCases
-- Test case 1: empty input should return true (vacuous truth)
def test1_s : Array Char := #[]
def test1_Expected : Bool := true

-- Test case 2: single digit
def test2_s : Array Char := #[ '7' ]
def test2_Expected : Bool := true

-- Test case 3: single non-digit
def test3_s : Array Char := #[ 'a' ]
def test3_Expected : Bool := false

-- Test case 4: multiple digits
def test4_s : Array Char := #[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' ]
def test4_Expected : Bool := true

-- Test case 5: contains a letter among digits
def test5_s : Array Char := #[ '1', 'a', '3' ]
def test5_Expected : Bool := false

-- Test case 6: contains whitespace
def test6_s : Array Char := #[ '1', ' ', '2' ]
def test6_Expected : Bool := false

-- Test case 7: contains punctuation
def test7_s : Array Char := #[ '9', '-', '0' ]
def test7_Expected : Bool := false

-- Test case 8: boundary digits only
def test8_s : Array Char := #[ '0', '9' ]
def test8_Expected : Bool := true

-- Test case 9: non-ASCII digit-like character (Arabic-Indic digit nine)
-- `Char.isDigit` checks only ASCII digits, so this should be false.
def test9_s : Array Char := #[ '٩' ]
def test9_Expected : Bool := false

-- Recommend to validate: empty input, singleton digit/non-digit, mixed content
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
