/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1cc89a42-b5ff-431c-86c1-893f2b608d54

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int) : VerinaSpec.ComputeIsEven_precond x ↔ LLMSpec.precondition x

- theorem postcondition_equiv (x : Int) (result : Bool) : LLMSpec.precondition x →
  (VerinaSpec.ComputeIsEven_postcond x result ↔ LLMSpec.postcondition x result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def ComputeIsEven_precond (x : Int) : Prop :=
  True

def ComputeIsEven_postcond (x : Int) (result: Bool) :=
  result = true ↔ ∃ k : Int, x = 2 * k

end VerinaSpec

namespace LLMSpec

def precondition (x : Int) : Prop :=
  True

def postcondition (x : Int) (result : Bool) : Prop :=
  (result = true ↔ x % 2 = 0)

end LLMSpec

section Proof

theorem precondition_equiv (x : Int) : VerinaSpec.ComputeIsEven_precond x ↔ LLMSpec.precondition x := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.ComputeIsEven_precond, LLMSpec.precondition]

theorem postcondition_equiv (x : Int) (result : Bool) : LLMSpec.precondition x →
  (VerinaSpec.ComputeIsEven_postcond x result ↔ LLMSpec.postcondition x result) := by
  unfold VerinaSpec.ComputeIsEven_postcond LLMSpec.postcondition; aesop;

end Proof