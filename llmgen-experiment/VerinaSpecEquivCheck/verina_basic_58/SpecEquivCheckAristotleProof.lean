/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ae8f9662-dc18-4e5a-af7d-1f838f90ba92

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (s : Array Int) : VerinaSpec.double_array_elements_precond s ↔ LLMSpec.precondition s

- theorem postcondition_equiv (s : Array Int) (result : Array Int) : LLMSpec.precondition s →
  (VerinaSpec.double_array_elements_postcond s result ↔ LLMSpec.postcondition s result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def double_array_elements_precond (s : Array Int) : Prop :=
  True

def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s

def double_array_elements_postcond (s : Array Int) (result: Array Int) :=
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!

end VerinaSpec

namespace LLMSpec

-- No additional helper definitions are required.

def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ (i : Nat), i < s.size → result[i]! = (2 : Int) * s[i]!

end LLMSpec

section Proof

theorem precondition_equiv (s : Array Int) : VerinaSpec.double_array_elements_precond s ↔ LLMSpec.precondition s := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.double_array_elements_precond, LLMSpec.precondition]

theorem postcondition_equiv (s : Array Int) (result : Array Int) : LLMSpec.precondition s →
  (VerinaSpec.double_array_elements_postcond s result ↔ LLMSpec.postcondition s result) := by
  -- Since the preconditions are the same, the postconditions must also be the same.
  simp [VerinaSpec.double_array_elements_postcond, LLMSpec.postcondition]

end Proof