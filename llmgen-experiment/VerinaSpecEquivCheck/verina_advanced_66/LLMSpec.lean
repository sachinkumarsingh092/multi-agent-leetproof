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
    ReverseWords: reverse the order of words in an input string.
    Natural language breakdown:
    1. The input is a string that may contain leading spaces, trailing spaces, or multiple spaces between words.
    2. A word is a maximal contiguous sequence of characters that are not the ASCII space character ' '.
    3. The output contains exactly the same words as the input, but in reverse order.
    4. The characters inside each word are unchanged.
    5. The output must be space-normalized: words are separated by exactly one ASCII space ' ', and there are no leading or trailing spaces.
    6. If the input contains no words (empty or all spaces), the output is the empty string.
-/

section Specs
-- We treat the ASCII space ' ' as the only separator.
def isSpace (c : Char) : Bool := c = ' '

-- A list of characters forms a nonempty word iff it contains no ASCII spaces.
def isWordChars (w : List Char) : Prop :=
  w ≠ [] ∧ ∀ (c : Char), c ∈ w → c ≠ ' '

def isWordList (ws : List (List Char)) : Prop :=
  ∀ (w : List Char), w ∈ ws → isWordChars w

-- Observe the words of a character list by splitting on ASCII space and dropping empty chunks.
-- This corresponds to maximal contiguous non-space blocks.
def wordsOfChars (cs : List Char) : List (List Char) :=
  (cs.splitOn ' ').filter (fun w => w ≠ [])

-- No two consecutive ASCII spaces in a list of characters.
def noConsecutiveSpaces (cs : List Char) : Prop :=
  ∀ (i : Nat), i + 1 < cs.length → ¬(cs[i]! = ' ' ∧ cs[i + 1]! = ' ')

-- A character list is space-normalized iff it is empty, or it has:
-- - no leading ASCII space,
-- - no trailing ASCII space,
-- - no consecutive ASCII spaces.
def normalizedSpaces (cs : List Char) : Prop :=
  cs = [] ∨
    (cs.head? ≠ some ' ' ∧
     cs.getLast? ≠ some ' ' ∧
     noConsecutiveSpaces cs)

def precondition (words_str : String) : Prop :=
  True

def postcondition (words_str : String) (result : String) : Prop :=
  normalizedSpaces result.data ∧
  isWordList (wordsOfChars words_str.data) ∧
  isWordList (wordsOfChars result.data) ∧
  wordsOfChars result.data = (wordsOfChars words_str.data).reverse
end Specs

section Impl
method ReverseWords (words_str : String)
  return (result : String)
  require precondition words_str
  ensures postcondition words_str result
  do
    pure ""  -- placeholder

prove_correct ReverseWords by sorry
end Impl

section TestCases
-- Test case 1: leading/trailing and multiple spaces (example)
-- Input words: ["hello", "world"], output should be "world hello".
def test1_words_str : String := "  hello   world  "
def test1_Expected : String := "world hello"

-- Test case 2: empty string
-- No words -> empty output.
def test2_words_str : String := ""
def test2_Expected : String := ""

-- Test case 3: only spaces
-- No words -> empty output.
def test3_words_str : String := "     "
def test3_Expected : String := ""

-- Test case 4: single word, no spaces
-- Reversal of singleton is itself.
def test4_words_str : String := "Lean"
def test4_Expected : String := "Lean"

-- Test case 5: already normalized two words
-- Output should be the two words swapped.
def test5_words_str : String := "a b"
def test5_Expected : String := "b a"

-- Test case 6: multiple spaces between words, no leading/trailing
-- Output should be normalized.
def test6_words_str : String := "a   b    c"
def test6_Expected : String := "c b a"

-- Test case 7: leading spaces only
-- Output has no leading/trailing spaces.
def test7_words_str : String := "   x y"
def test7_Expected : String := "y x"

-- Test case 8: trailing spaces only
-- Output has no leading/trailing spaces.
def test8_words_str : String := "x y   "
def test8_Expected : String := "y x"

-- Test case 9: punctuation inside words is preserved
-- Words are non-space chunks; punctuation is part of a word.
def test9_words_str : String := "hi, there!  lean4"
def test9_Expected : String := "lean4 there! hi,"

-- Recommend to validate: empty input, all-space input, multi-space normalization
end TestCases
