/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d4b75cdc-25fe-4c58-a48f-b22bb46c27bc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.concat_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.concat_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) :=
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

end VerinaSpec

namespace LLMSpec

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size + b.size ∧
  (∀ (i : Nat), i < a.size → result[i]! = a[i]!) ∧
  (∀ (j : Nat), j < b.size → result[a.size + j]! = b[j]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.concat_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are True, they are trivially equivalent.
  simp [VerinaSpec.concat_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.concat_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- By definition of `VerinaSpec.concat_postcond` and `LLMSpec.postcondition`, we can split the conjunction into two implications.
  simp [VerinaSpec.concat_postcond, LLMSpec.postcondition];
  -- Since addition is commutative, the two conditions are equivalent.
  intros h_pre h_size h_eq
  simp [add_comm]

end Proof