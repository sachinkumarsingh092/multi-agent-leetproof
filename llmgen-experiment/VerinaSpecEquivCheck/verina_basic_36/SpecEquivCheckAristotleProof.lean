/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f9879045-3bf1-4c42-8443-808a926db5fe

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.replaceWithColon_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.replaceWithColon_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false

def replaceWithColon_precond (s : String) : Prop :=
  True

def replaceWithColon_postcond (s : String) (result: String) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < s.length →
    (isSpaceCommaDot cs[i]! → cs'[i]! = ':') ∧
    (¬isSpaceCommaDot cs[i]! → cs'[i]! = cs[i]!))

end VerinaSpec

namespace LLMSpec

-- Helper: identify the separator characters that must be replaced.

def isSepChar (c : Char) : Bool :=
  (c = ' ') || (c = ',') || (c = '.')

-- Helper: the output character corresponding to an input character.

def replaceSep (c : Char) : Char :=
  if isSepChar c then ':' else c

-- Preconditions

def precondition (s : String) : Prop :=
  True

-- Postconditions
-- We specify behavior over the underlying character lists (`data`) to avoid any ambiguity
-- about the relation between `String.length` and indexing.

def postcondition (s : String) (result : String) : Prop :=
  result.data.length = s.data.length ∧
  ∀ (i : Nat), i < s.data.length →
    result.data[i]! = replaceSep (s.data[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.replaceWithColon_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.replaceWithColon_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : String) : LLMSpec.precondition s →
  (VerinaSpec.replaceWithColon_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- Since the preconditions are the same, we can focus on the postconditions.
  intro h_pre
  simp [VerinaSpec.replaceWithColon_postcond, LLMSpec.postcondition];
  -- The two postconditions are equivalent because they both check the same conditions on the characters.
  simp [VerinaSpec.isSpaceCommaDot, LLMSpec.replaceSep];
  -- By definition of `replaceWithColon` and `replaceSep`, we can show that they are equivalent.
  apply Iff.intro;
  · -- By definition of `replaceSep`, we can split the conjunction into two implications.
    intro h
    obtain ⟨h_len, h_char⟩ := h;
    refine' ⟨ by simpa using h_len, fun i hi => _ ⟩ ; specialize h_char i hi ; unfold LLMSpec.isSepChar at * ; aesop;
  · -- By definition of `isSepChar`, we know that `isSepChar c` is true if and only if `c` is a space, comma, or dot.
    intro h
    obtain ⟨h_len, h_char⟩ := h
    simp [LLMSpec.isSepChar] at h_char;
    exact ⟨ h_len, fun i hi => by specialize h_char i hi; aesop ⟩

end Proof