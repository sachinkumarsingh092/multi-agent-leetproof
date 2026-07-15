/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6dfdb6f2-f6d2-4c22-b9e6-0dffe914e17c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.countDigits_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : Nat) : LLMSpec.precondition s →
  (VerinaSpec.countDigits_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def countDigits_precond (s : String) : Prop :=
  True

def countDigits_postcond (s : String) (result: Nat) :=
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0

end VerinaSpec

namespace LLMSpec

-- Helper: reuse the standard digit predicate on characters.
def isDigitChar (c : Char) : Bool :=
  c.isDigit

-- We count digits in the character list of the string.
def digitCount (s : String) : Nat :=
  s.toList.countP (fun c => isDigitChar c)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : Nat) : Prop :=
  result = digitCount s

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.countDigits_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.countDigits_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : Nat) : LLMSpec.precondition s →
  (VerinaSpec.countDigits_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- Since the VerinaSpec's postcondition is defined as the result minus the length of the filtered list equals zero, and the LLMSpec's postcondition is the result equals the digit count, which is the length of the filtered list, then the two postconditions are equivalent.
  simp [VerinaSpec.countDigits_postcond, LLMSpec.postcondition];
  -- By definition of `digitCount`, we know that `digitCount s` is equal to the length of the filtered list of digits in `s.data`.
  have h_digitCount : LLMSpec.digitCount s = (List.filter VerinaSpec.isDigit s.data).length := by
    -- By definition of `countP`, we can rewrite the goal using the equivalence of the filtered list and the list of digits.
    have h_countP_eq_filter : ∀ (l : List Char), List.countP (fun c => c.isDigit) l = List.length (List.filter (fun c => c.isDigit) l) := by
      grind;
    convert h_countP_eq_filter s.data using 1;
    congr! 2;
    ext c; unfold VerinaSpec.isDigit; simp +decide [ Char.isDigit ] ;
    exact?;
  grind

end Proof