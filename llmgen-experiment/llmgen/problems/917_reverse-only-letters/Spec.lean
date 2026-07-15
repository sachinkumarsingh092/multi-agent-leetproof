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
    917. Reverse Only Letters: Reverse only the English letters in a character sequence, keeping non-letters fixed.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. Input is a finite sequence of characters.
    2. A character is considered an English letter exactly when it is an ASCII uppercase letter ('A'..'Z') or an ASCII lowercase letter ('a'..'z').
    3. Every non-letter character must stay at the same index in the output.
    4. The set of indices that contain letters must be the same in input and output.
    5. Reading only the letters from left to right in the output yields the reverse of the letters read from left to right in the input.
    6. The output has the same length as the input.
-/

section Specs
-- Helper predicate: ASCII uppercase letter ('A'..'Z').
def isAsciiUpper (c : Char) : Bool :=
  ('A'.toNat ≤ c.toNat) && (c.toNat ≤ 'Z'.toNat)

-- Helper predicate: ASCII lowercase letter ('a'..'z').
def isAsciiLower (c : Char) : Bool :=
  ('a'.toNat ≤ c.toNat) && (c.toNat ≤ 'z'.toNat)

-- Helper predicate: English letter (ASCII) is upper or lower.
def isLetter (c : Char) : Bool :=
  isAsciiUpper c || isAsciiLower c

-- Helper: extract the subsequence of letters.
def letters (s : List Char) : List Char :=
  s.filter (fun c => isLetter c)

-- No special input restrictions.
def precondition (s : List Char) : Prop :=
  True

-- Postcondition: length preserved; non-letters fixed; letter mask preserved; letters reversed.
def postcondition (s : List Char) (result : List Char) : Prop :=
  result.length = s.length ∧
  (∀ (i : Nat), i < s.length → (isLetter s[i]! = false) → result[i]! = s[i]!) ∧
  (∀ (i : Nat), i < s.length → isLetter result[i]! = isLetter s[i]!) ∧
  letters result = (letters s).reverse
end Specs

section Impl
method ReverseOnlyLetters (s : List Char)
  return (result : List Char)
  require precondition s
  ensures postcondition s result
  do
  -- placeholder body (must typecheck)
  pure s

end Impl

section TestCases
-- Test case 1: example 1
-- Input: "ab-cd"  Output: "dc-ba"
def test1_s : List Char := ['a','b','-','c','d']
def test1_Expected : List Char := ['d','c','-','b','a']

-- Test case 2: example 2
-- Input: "a-bC-dEf-ghIj"  Output: "j-Ih-gfE-dCba"
def test2_s : List Char := ['a','-','b','C','-','d','E','f','-','g','h','I','j']
def test2_Expected : List Char := ['j','-','I','h','-','g','f','E','-','d','C','b','a']

-- Test case 3: example 3
-- Input: "Test1ng-Leet=code-Q!"  Output: "Qedo1ct-eeLg=ntse-T!"
def test3_s : List Char :=
  ['T','e','s','t','1','n','g','-','L','e','e','t','=','c','o','d','e','-','Q','!']
def test3_Expected : List Char :=
  ['Q','e','d','o','1','c','t','-','e','e','L','g','=','n','t','s','e','-','T','!']

-- Test case 4: empty input

def test4_s : List Char := []
def test4_Expected : List Char := []

-- Test case 5: only letters (all reversed)

def test5_s : List Char := ['A','b','C','d']
def test5_Expected : List Char := ['d','C','b','A']

-- Test case 6: only non-letters (unchanged)

def test6_s : List Char := ['-','1','_','!']
def test6_Expected : List Char := ['-','1','_','!']

-- Test case 7: single character that is a letter

def test7_s : List Char := ['z']
def test7_Expected : List Char := ['z']

-- Test case 8: single character that is not a letter

def test8_s : List Char := ['?']
def test8_Expected : List Char := ['?']

-- Test case 9: letters separated by digits and punctuation
-- Input letters: a b c d e; reversed: e d c b a
-- Non-letters stay in place.

def test9_s : List Char := ['a','1','b','2','-','c','3','d','4','e']
def test9_Expected : List Char := ['e','1','d','2','-','c','3','b','4','a']

-- Recommend to validate: empty input, inputs with only non-letters, inputs mixing letters/non-letters
end TestCases
