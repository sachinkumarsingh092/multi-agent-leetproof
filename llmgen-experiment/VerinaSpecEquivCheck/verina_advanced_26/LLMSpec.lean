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
    PhoneKeypadLetterCombinations: generate all possible letter combinations from a string of digit characters using telephone keypad mapping.
    Natural language breakdown:
    1. The input is a String of characters; it may be empty.
    2. Valid digit characters are exactly '2','3','4','5','6','7','8','9'.
    3. Each valid digit maps to a fixed nonempty list of lowercase letters, as on a telephone keypad.
    4. Any other character (including '0','1', non-digits, punctuation, etc.) is invalid.
    5. If the input is empty, the output must be the empty list.
    6. If the input contains any invalid character, the output must be the empty list.
    7. Otherwise, each output string has the same length as the input.
    8. For each index i, the output character at i must be one of the letters mapped from the input digit at i.
    9. The output contains all such valid combinations (completeness) and contains no duplicates.
    10. To make the output uniquely determined, the output list is required to be sorted under the default String order.
-/

section Specs
-- Helper: validity of a keypad digit character.
def validDigit (c : Char) : Bool :=
  c = '2' || c = '3' || c = '4' || c = '5' || c = '6' || c = '7' || c = '8' || c = '9'

-- Helper: keypad letter mapping.
def lettersOf (c : Char) : List Char :=
  if c = '2' then ['a', 'b', 'c'] else
  if c = '3' then ['d', 'e', 'f'] else
  if c = '4' then ['g', 'h', 'i'] else
  if c = '5' then ['j', 'k', 'l'] else
  if c = '6' then ['m', 'n', 'o'] else
  if c = '7' then ['p', 'q', 'r', 's'] else
  if c = '8' then ['t', 'u', 'v'] else
  if c = '9' then ['w', 'x', 'y', 'z'] else
  []

def allValidDigits (ds : List Char) : Bool :=
  ds.all validDigit

-- A character-list `combo` is a valid combination for `ds` iff
-- it has the same length and each position picks a letter allowed by that digit.
def isValidCombinationFor (ds : List Char) (combo : List Char) : Prop :=
  combo.length = ds.length ∧
  ∀ (i : Nat), i < ds.length → combo.get! i ∈ lettersOf (ds.get! i)

-- The function is total: it must return [] on empty/invalid input.
def precondition (digits : String) : Prop :=
  True

def postcondition (digits : String) (result : List String) : Prop :=
  let ds : List Char := digits.data
  ((ds = [] ∨ allValidDigits ds = false) → result = []) ∧
  ((ds ≠ [] ∧ allValidDigits ds = true) →
      (∀ (s : String), s ∈ result → isValidCombinationFor ds s.data) ∧
      (∀ (combo : List Char), isValidCombinationFor ds combo → (String.mk combo) ∈ result) ∧
      result.Nodup ∧
      result.Sorted (fun a b => a ≤ b))
end Specs

section Impl
method PhoneKeypadLetterCombinations (digits : String)
  return (result : List String)
  require precondition digits
  ensures postcondition digits result
  do
  pure ([])

end Impl

section TestCases
-- Test case 1: empty input => empty output
-- (No explicit example is given in the statement; we use the empty-input rule.)
def test1_digits : String := ""
def test1_Expected : List String := []

-- Test case 2: single valid digit "2"
def test2_digits : String := "2"
def test2_Expected : List String := ["a", "b", "c"]

-- Test case 3: two digits "23" (3 * 3 = 9 combinations)
def test3_digits : String := "23"
def test3_Expected : List String :=
  ["ad", "ae", "af",
   "bd", "be", "bf",
   "cd", "ce", "cf"]

-- Test case 4: invalid digit "1" => empty
def test4_digits : String := "1"
def test4_Expected : List String := []

-- Test case 5: invalid digit "0" => empty
def test5_digits : String := "0"
def test5_Expected : List String := []

-- Test case 6: contains non-digit character => empty
def test6_digits : String := "2a"
def test6_Expected : List String := []

-- Test case 7: boundary valid digit "9"
def test7_digits : String := "9"
def test7_Expected : List String := ["w", "x", "y", "z"]

-- Test case 8: valid digit "8" (typical middle case)
def test8_digits : String := "8"
def test8_Expected : List String := ["t", "u", "v"]

-- Test case 9: repeated digits "22" (3 * 3 = 9 combinations)
def test9_digits : String := "22"
def test9_Expected : List String :=
  ["aa", "ab", "ac",
   "ba", "bb", "bc",
   "ca", "cb", "cc"]

-- Recommend to validate: empty input, invalid digits (0/1), non-digit characters, boundary digits (2/9), typical digit (8), repeated digits, multi-digit cartesian growth
end TestCases
