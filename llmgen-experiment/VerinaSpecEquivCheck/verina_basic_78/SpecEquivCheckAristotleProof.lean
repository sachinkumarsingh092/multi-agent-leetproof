/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 289b35b2-3d79-4e0e-8fb1-fd9c201257f4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (x : Int) (y : Int) : VerinaSpec.MultipleReturns_precond x y ↔ LLMSpec.precondition x y

- theorem postcondition_equiv (x : Int) (y : Int) (result : (Int × Int)) : LLMSpec.precondition x y →
  (VerinaSpec.MultipleReturns_postcond x y result ↔ LLMSpec.postcondition x y result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  True

def MultipleReturns_postcond (x : Int) (y : Int) (result: (Int × Int)) :=
  result.1 = x + y ∧ result.2 + y = x

end VerinaSpec

namespace LLMSpec

-- No helper functions are required: we use Int addition/subtraction and product projections.

def precondition (x : Int) (y : Int) : Prop :=
  True

def postcondition (x : Int) (y : Int) (result : (Int × Int)) : Prop :=
  result.1 = x + y ∧ result.2 = x - y

end LLMSpec

section Proof

theorem precondition_equiv (x : Int) (y : Int) : VerinaSpec.MultipleReturns_precond x y ↔ LLMSpec.precondition x y := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.MultipleReturns_precond, LLMSpec.precondition]

theorem postcondition_equiv (x : Int) (y : Int) (result : (Int × Int)) : LLMSpec.precondition x y →
  (VerinaSpec.MultipleReturns_postcond x y result ↔ LLMSpec.postcondition x y result) := by
  -- The postconditions are identical, so the equivalence holds by definition.
  simp [VerinaSpec.MultipleReturns_postcond, LLMSpec.postcondition];
  -- The equivalence follows directly from the properties of addition and subtraction.
  intros h_pre h_eq
  apply Iff.intro (fun h => by linarith) (fun h => by linarith)

end Proof