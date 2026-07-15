/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 150f3368-dac7-4bc8-9dac-01b9c0ae7e25

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) (p : String) : VerinaSpec.Match_precond s p ↔ LLMSpec.precondition s.toList.toArray p.toList.toArray

- theorem postcondition_equiv (s : String) (p : String) (result : Bool) : LLMSpec.precondition s.toList.toArray p.toList.toArray →
  (VerinaSpec.Match_postcond s p result ↔ LLMSpec.postcondition s.toList.toArray p.toList.toArray result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def Match_precond (s : String) (p : String) : Prop :=
  s.toList.length = p.toList.length

def Match_postcond (s : String) (p : String) (result: Bool) :=
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))

end VerinaSpec

namespace LLMSpec

-- A pattern character matches a text character if it is '?' or it equals the text character.
def charMatches (sc : Char) (pc : Char) : Prop :=
  pc = '?' ∨ pc = sc

-- Pointwise match predicate for equal-length arrays.
def matchesPattern (s : Array Char) (p : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → charMatches (s[i]!) (p[i]!)

-- The note states we may assume equal length, so we enforce it as a precondition.
def precondition (s : Array Char) (p : Array Char) : Prop :=
  s.size = p.size

def postcondition (s : Array Char) (p : Array Char) (result : Bool) : Prop :=
  (result = true ↔ matchesPattern s p) ∧
  (result = false ↔ ¬ matchesPattern s p)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) (p : String) : VerinaSpec.Match_precond s p ↔ LLMSpec.precondition s.toList.toArray p.toList.toArray := by
  -- The length of a string is equal to the length of its underlying list.
  simp [VerinaSpec.Match_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (p : String) (result : Bool) : LLMSpec.precondition s.toList.toArray p.toList.toArray →
  (VerinaSpec.Match_postcond s p result ↔ LLMSpec.postcondition s.toList.toArray p.toList.toArray result) := by
  -- If the precondition holds, then the postconditions are equivalent because the lengths are equal.
  intro h_pre
  simp [VerinaSpec.Match_postcond, LLMSpec.postcondition, h_pre];
  -- By definition of `matchesPattern`, we know that if the pattern matches the text, then for every position `n`, the characters are either equal or the pattern has a '?' because the pattern is '?'. Therefore, the equivalence holds.
  simp [LLMSpec.matchesPattern, LLMSpec.charMatches];
  grind +ring

end Proof