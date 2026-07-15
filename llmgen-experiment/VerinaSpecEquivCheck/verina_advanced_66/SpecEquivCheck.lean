import Mathlib.Tactic

namespace VerinaSpec


def reverseWords_precond (words_str : String) : Prop :=
  True

def reverseWords_postcond (words_str : String) (result: String) : Prop :=
  ∃ words : List String,
    (words = (words_str.splitOn " ").filter (fun w => w ≠ "")) ∧
    result = String.intercalate " " (words.reverse)

end VerinaSpec

namespace LLMSpec

def isSpace (c : Char) : Bool := c = ' '

def isWordChars (w : List Char) : Prop :=
  w ≠ [] ∧ ∀ (c : Char), c ∈ w → c ≠ ' '

def isWordList (ws : List (List Char)) : Prop :=
  ∀ (w : List Char), w ∈ ws → isWordChars w

def wordsOfChars (cs : List Char) : List (List Char) :=
  (cs.splitOn ' ').filter (fun w => w ≠ [])

def noConsecutiveSpaces (cs : List Char) : Prop :=
  ∀ (i : Nat), i + 1 < cs.length → ¬(cs[i]! = ' ' ∧ cs[i + 1]! = ' ')

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
end LLMSpec

section Proof

theorem precondition_equiv (words_str : String) :
  VerinaSpec.reverseWords_precond words_str ↔ LLMSpec.precondition words_str := by
  sorry

theorem postcondition_equiv (words_str : String) (result: String) :
  LLMSpec.precondition words_str →
  (VerinaSpec.reverseWords_postcond words_str result ↔ LLMSpec.postcondition words_str result) := by
  sorry

end Proof
