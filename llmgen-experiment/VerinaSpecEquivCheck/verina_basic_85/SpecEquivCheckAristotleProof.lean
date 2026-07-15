/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8cb19f00-7fa4-461e-862a-c572dcbf1f9e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.reverse_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.reverse_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def reverse_precond (a : Array Int) : Prop :=
  True

def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr

def reverse_postcond (a : Array Int) (result: Array Int) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)

end VerinaSpec

namespace LLMSpec

-- No helper functions are required for this specification.

def precondition (a : Array Int) : Prop :=
  True

-- The postcondition is purely relational:
-- it characterizes the output by size preservation and index-wise reverse correspondence.
-- Note: we use Nat subtraction (a.size - 1 - i). When i < a.size, this denotes the
-- intended mirror index; Array indexing with `!` is total, so the property is decidable
-- and simple to state.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ (i : Nat), i < a.size → result[i]! = a[(a.size - 1 - i)]!

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.reverse_precond a ↔ LLMSpec.precondition a := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.reverse_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.reverse_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- Since both postconditions require the size to be the same, the second part of the postconditions must be equivalent.
  intros h_pre
  simp [VerinaSpec.reverse_postcond, LLMSpec.postcondition]

end Proof