/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4ed1e01e-d649-4acb-91dc-f7a9b284b18f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (n : Nat) : VerinaSpec.isPerfectSquare_precond n ↔ LLMSpec.precondition n

- theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isPerfectSquare_postcond n result ↔ LLMSpec.postcondition n result)
-/

import Mathlib.Tactic

import Mathlib


namespace VerinaSpec

def isPerfectSquare_precond (n : Nat) : Prop :=
  True

def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop :=
  result ↔ ∃ i : Nat, i * i = n

end VerinaSpec

namespace LLMSpec

-- Helper predicate: proposition-level notion of perfect square.
-- We use multiplication (k * k) as squaring.
def IsPerfectSquareProp (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsPerfectSquareProp n)

end LLMSpec

section Proof

theorem precondition_equiv (n : Nat) : VerinaSpec.isPerfectSquare_precond n ↔ LLMSpec.precondition n := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.isPerfectSquare_precond, LLMSpec.precondition]

theorem postcondition_equiv (n : Nat) (result : Bool) : LLMSpec.precondition n →
  (VerinaSpec.isPerfectSquare_postcond n result ↔ LLMSpec.postcondition n result) := by
  -- By definition of `IsPerfectSquareProp`, we know that `IsPerfectSquareProp n` is equivalent to `∃ k : ℕ, k * k = n`.
  simp [LLMSpec.postcondition, VerinaSpec.isPerfectSquare_postcond];
  -- By definition of `IsPerfectSquareProp`, we know that `IsPerfectSquareProp n` is equivalent to `∃ k : ℕ, k * k = n`. Therefore, the equivalence holds.
  simp [LLMSpec.IsPerfectSquareProp]

end Proof