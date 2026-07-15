/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d3b6945c-2798-4d9c-be4c-24465fc8d1c9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.arrayProduct_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.arrayProduct_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c

def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) :=
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)

end VerinaSpec

namespace LLMSpec

-- Helper: the value to use for a missing element (matches the problem statement).
-- This is not needed under the equal-length precondition, but documents the intended default.
def missingDefault : Int := 0

def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  (∀ (i : Nat), i < result.size → result[i]! = a[i]! * b[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.arrayProduct_precond a b ↔ LLMSpec.precondition a b := by
  -- The preconditions are equivalent because they are the same condition.
  simp [VerinaSpec.arrayProduct_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.arrayProduct_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  unfold VerinaSpec.arrayProduct_postcond LLMSpec.postcondition; aesop;

end Proof