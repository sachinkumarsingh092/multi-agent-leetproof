/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4e47947c-d40f-44fa-be92-89bdc4d2e8d9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (N : Nat) : VerinaSpec.SquareRoot_precond N ↔ LLMSpec.precondition N

- theorem postcondition_equiv (N : Nat) (result : Nat) : LLMSpec.precondition N →
  (VerinaSpec.SquareRoot_postcond N result ↔ LLMSpec.postcondition N result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def SquareRoot_precond (N : Nat) : Prop :=
  True

def SquareRoot_postcond (N : Nat) (result: Nat) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)

end VerinaSpec

namespace LLMSpec

-- No helper functions are required: the specification is expressed directly
-- using multiplication and ordering on Nat.

def precondition (N : Nat) : Prop :=
  True

def postcondition (N : Nat) (result : Nat) : Prop :=
  result * result ≤ N ∧
  N < (result + 1) * (result + 1)

end LLMSpec

section Proof

theorem precondition_equiv (N : Nat) : VerinaSpec.SquareRoot_precond N ↔ LLMSpec.precondition N := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.SquareRoot_precond, LLMSpec.precondition]

theorem postcondition_equiv (N : Nat) (result : Nat) : LLMSpec.precondition N →
  (VerinaSpec.SquareRoot_postcond N result ↔ LLMSpec.postcondition N result) := by
  -- The postcondition for VerinaSpec and LLMSpec are defined identically, so the equivalence holds trivially.
  simp [VerinaSpec.SquareRoot_postcond, LLMSpec.postcondition]

end Proof