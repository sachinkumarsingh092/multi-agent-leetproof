/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e03f1de4-6d69-437a-9e4c-d56c36c87b61

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : VerinaSpec.insert_precond oline l nl p atPos ↔ LLMSpec.precondition oline l nl p atPos

- theorem postcondition_equiv (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) : LLMSpec.precondition oline l nl p atPos →
  (VerinaSpec.insert_postcond oline l nl p atPos result ↔ LLMSpec.postcondition oline l nl p atPos result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l

def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) :=
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)

end VerinaSpec

namespace LLMSpec

-- Preconditions described in the problem statement.
-- All bounds are on natural numbers, and ensure safe indexing in the postcondition.
def precondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l

-- Postcondition: `result` has size `l + p` and matches the intended piecewise content.
def postcondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat)
    (result : Array Char) : Prop :=
  result.size = l + p ∧
  -- Prefix before insertion position is preserved from `oline`.
  (∀ (i : Nat), i < atPos → result[i]! = oline[i]!) ∧
  -- Inserted segment equals the first `p` characters of `nl`.
  (∀ (i : Nat), i < p → result[atPos + i]! = nl[i]!) ∧
  -- Suffix after insertion position comes from `oline`'s prefix of length `l`, shifted by `p`.
  (∀ (i : Nat), i < l - atPos → result[atPos + p + i]! = oline[atPos + i]!)

end LLMSpec

section Proof

theorem precondition_equiv (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : VerinaSpec.insert_precond oline l nl p atPos ↔ LLMSpec.precondition oline l nl p atPos := by
  -- By definition of `insert_precond` and `precondition`, they are equivalent.
  simp [VerinaSpec.insert_precond, LLMSpec.precondition]

theorem postcondition_equiv (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) : LLMSpec.precondition oline l nl p atPos →
  (VerinaSpec.insert_postcond oline l nl p atPos result ↔ LLMSpec.postcondition oline l nl p atPos result) := by
  -- Since the preconditions are the same, the postconditions are equivalent by definition.
  intros h_pre
  simp [VerinaSpec.insert_postcond, LLMSpec.postcondition];
  grind

end Proof