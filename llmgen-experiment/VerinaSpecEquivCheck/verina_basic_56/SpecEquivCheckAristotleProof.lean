/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 13aacbb5-6c8c-48de-a20d-49b9c278a5ec

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : VerinaSpec.copy_precond src sStart dest dStart len ↔ LLMSpec.precondition src sStart dest dStart len

- theorem postcondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result : Array Int) : LLMSpec.precondition src sStart dest dStart len →
  (VerinaSpec.copy_postcond src sStart dest dStart len result ↔ LLMSpec.postcondition src sStart dest dStart len result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len

def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n

def copy_postcond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result: Array Int) :=
  result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)

end VerinaSpec

namespace LLMSpec

-- Preconditions: the source and destination segments are within bounds.
def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  src.size ≥ sStart + len ∧ dest.size ≥ dStart + len

-- Postconditions: size preserved, outside segment unchanged, inside segment copied.
def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
    (result : Array Int) : Prop :=
  result.size = dest.size ∧
  (∀ (i : Nat), i < dStart → result[i]! = dest[i]!) ∧
  (∀ (k : Nat), k < len → result[dStart + k]! = src[sStart + k]!) ∧
  (∀ (i : Nat), dStart + len ≤ i → i < dest.size → result[i]! = dest[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : VerinaSpec.copy_precond src sStart dest dStart len ↔ LLMSpec.precondition src sStart dest dStart len := by
  -- The preconditions are identical, so their equivalence is trivial.
  simp [VerinaSpec.copy_precond, LLMSpec.precondition]

theorem postcondition_equiv (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result : Array Int) : LLMSpec.precondition src sStart dest dStart len →
  (VerinaSpec.copy_postcond src sStart dest dStart len result ↔ LLMSpec.postcondition src sStart dest dStart len result) := by
  unfold LLMSpec.precondition VerinaSpec.copy_postcond LLMSpec.postcondition; aesop;

end Proof