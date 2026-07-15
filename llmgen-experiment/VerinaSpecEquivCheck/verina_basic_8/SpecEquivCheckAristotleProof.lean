/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bca4fb5f-80a1-48c9-8bba-309a4ec65827

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Int) (b : Int) : VerinaSpec.myMin_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Int) (b : Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.myMin_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def myMin_precond (a : Int) (b : Int) : Prop :=
  True

def myMin_postcond (a : Int) (b : Int) (result: Int) :=
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)

end VerinaSpec

namespace LLMSpec

-- No input constraints are needed for taking the minimum of two integers.

def precondition (a : Int) (b : Int) : Prop :=
  True

-- The result is a lower bound of both inputs and is equal to one of them.
-- This uniquely characterizes the mathematical minimum, while allowing either
-- input to be returned in the equality case.
def postcondition (a : Int) (b : Int) (result : Int) : Prop :=
  result ≤ a ∧ result ≤ b ∧ (result = a ∨ result = b)

end LLMSpec

section Proof

theorem precondition_equiv (a : Int) (b : Int) : VerinaSpec.myMin_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.myMin_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Int) (b : Int) (result : Int) : LLMSpec.precondition a b →
  (VerinaSpec.myMin_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- The postconditions are equivalent because they are the same statement.
  simp [VerinaSpec.myMin_postcond, LLMSpec.postcondition];
  -- The equivalence follows from the associativity of logical AND.
  simp [and_assoc]

end Proof