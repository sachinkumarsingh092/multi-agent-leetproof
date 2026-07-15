/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f73a66cb-2400-4fc1-a838-154dbcaebfce

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : String) : VerinaSpec.allDigits_precond s ↔ LLMSpec.precondition s.toList.toArray

- theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s.toList.toArray →
  (VerinaSpec.allDigits_postcond s result ↔ LLMSpec.postcondition s.toList.toArray result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')

def allDigits_precond (s : String) : Prop :=
  True

def allDigits_postcond (s : String) (result: Bool) :=
  (result = true ↔ ∀ c ∈ s.toList, isDigit c)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: every character in the array is an ASCII digit.
def allDigits (s : Array Char) : Prop :=
  ∀ (i : Nat), i < s.size → (s[i]!).isDigit = true

-- No preconditions.
def precondition (s : Array Char) : Prop :=
  True

def postcondition (s : Array Char) (result : Bool) : Prop :=
  (result = true ↔ allDigits s)

end LLMSpec

section Proof

theorem precondition_equiv (s : String) : VerinaSpec.allDigits_precond s ↔ LLMSpec.precondition s.toList.toArray := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.allDigits_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : String) (result : Bool) : LLMSpec.precondition s.toList.toArray →
  (VerinaSpec.allDigits_postcond s result ↔ LLMSpec.postcondition s.toList.toArray result) := by
  -- By definition of `allDigits`, we know that `allDigits s.toList.toArray` is equivalent to `∀ c ∈ s.toList, isDigit c`.
  simp [VerinaSpec.allDigits_postcond, LLMSpec.postcondition, LLMSpec.allDigits];
  -- The equivalence holds because the condition for the array implies the condition for the list and vice versa.
  intros h_precond
  apply Iff.intro;
  · aesop;
  · intro h c hc; obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hc; aesop;

end Proof