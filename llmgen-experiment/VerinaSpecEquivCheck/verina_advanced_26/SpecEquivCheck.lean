import Mathlib.Tactic

namespace VerinaSpec


def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

def letterCombinations_precond (digits : String) : Prop :=
  True

def letterCombinations_postcond (digits : String) (result: List String) : Prop :=
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)

end VerinaSpec

namespace LLMSpec

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

end LLMSpec

section Proof

theorem precondition_equiv (digits : String) :
  VerinaSpec.letterCombinations_precond digits ↔ LLMSpec.precondition digits := by
  sorry

theorem postcondition_equiv (digits : String) (result: List String) :
  LLMSpec.precondition digits →
  (VerinaSpec.letterCombinations_postcond digits result ↔ LLMSpec.postcondition digits result) := by
  sorry

end Proof
