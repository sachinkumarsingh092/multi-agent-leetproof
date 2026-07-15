import Mathlib.Tactic

namespace VerinaSpec


def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower

def allVowels_precond (s : String) : Prop :=
  True

def allVowels_postcond (s : String) (result: Bool) : Prop :=
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))

end VerinaSpec

namespace LLMSpec

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

end LLMSpec

section Proof

theorem precondition_equiv (s : String) :
  VerinaSpec.allVowels_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result: Bool) :
  LLMSpec.precondition s →
  (VerinaSpec.allVowels_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
