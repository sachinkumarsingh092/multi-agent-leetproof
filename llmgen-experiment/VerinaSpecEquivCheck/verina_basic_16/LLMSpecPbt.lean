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
    ReplaceCharInString: Replace every occurrence of a specified character with a new character.
    Natural language breakdown:
    1. The input is a sequence of characters `s`, an `oldChar`, and a `newChar`.
    2. The output is a new sequence of characters `result`.
    3. The output has the same length (size) as the input sequence.
    4. For each valid index i, if `s[i]` equals `oldChar`, then `result[i]` equals `newChar`.
    5. For each valid index i, if `s[i]` does not equal `oldChar`, then `result[i]` equals `s[i]`.
    6. There are no preconditions: the method is total for all inputs.
-/

section Specs
-- We model strings as `Array Char` (instead of `String`) to avoid `String` in specifications.

def precondition (s : Array Char) (oldChar : Char) (newChar : Char) : Prop :=
  True

def postcondition (s : Array Char) (oldChar : Char) (newChar : Char) (result : Array Char) : Prop :=
  result.size = s.size ∧
  (∀ (i : Nat), i < s.size →
    result[i]! = (if s[i]! = oldChar then newChar else s[i]!))
end Specs

section Impl
method ReplaceCharInString (s : Array Char) (oldChar : Char) (newChar : Char)
  return (result : Array Char)
  require precondition s oldChar newChar
  ensures postcondition s oldChar newChar result
  do
  -- Placeholder implementation only
  pure s

prove_correct ReplaceCharInString by sorry
end Impl

section TestCases
-- Test case 1: typical replacement with multiple occurrences
def test1_s : Array Char := #['a', 'b', 'a', 'c', 'a']
def test1_oldChar : Char := 'a'
def test1_newChar : Char := 'x'
def test1_Expected : Array Char := #['x', 'b', 'x', 'c', 'x']

-- Test case 2: empty input
def test2_s : Array Char := #[]
def test2_oldChar : Char := 'q'
def test2_newChar : Char := 'z'
def test2_Expected : Array Char := #[]

-- Test case 3: singleton where replacement happens
def test3_s : Array Char := #['p']
def test3_oldChar : Char := 'p'
def test3_newChar : Char := 'r'
def test3_Expected : Array Char := #['r']

-- Test case 4: singleton where replacement does not happen
def test4_s : Array Char := #['p']
def test4_oldChar : Char := 'x'
def test4_newChar : Char := 'r'
def test4_Expected : Array Char := #['p']

-- Test case 5: no occurrences of oldChar
def test5_s : Array Char := #['h', 'e', 'l', 'l', 'o']
def test5_oldChar : Char := 'z'
def test5_newChar : Char := 'y'
def test5_Expected : Array Char := #['h', 'e', 'l', 'l', 'o']

-- Test case 6: all characters are oldChar
def test6_s : Array Char := #['a', 'a', 'a', 'a']
def test6_oldChar : Char := 'a'
def test6_newChar : Char := 'b'
def test6_Expected : Array Char := #['b', 'b', 'b', 'b']

-- Test case 7: oldChar = newChar (result should equal input)
def test7_s : Array Char := #['m', 'a', 'p']
def test7_oldChar : Char := 'a'
def test7_newChar : Char := 'a'
def test7_Expected : Array Char := #['m', 'a', 'p']

-- Test case 8: replacement with a non-ASCII/unicode character
def test8_s : Array Char := #['λ', 'x', 'λ']
def test8_oldChar : Char := 'λ'
def test8_newChar : Char := 'π'
def test8_Expected : Array Char := #['π', 'x', 'π']

-- Test case 9: replacement with whitespace/newline
def test9_s : Array Char := #['a', '\n', 'b', '\n']
def test9_oldChar : Char := '\n'
def test9_newChar : Char := ' '
def test9_Expected : Array Char := #['a', ' ', 'b', ' ']
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Array Char) :
  result ≠ test9_Expected →
  ¬ postcondition test9_s test9_oldChar test9_newChar result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
