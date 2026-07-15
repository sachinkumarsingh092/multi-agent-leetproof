/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d48303d-8dc9-40de-9217-e3ffc99fb43f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Int) : VerinaSpec.append_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.append_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def append_precond (a : Array Int) (b : Int) : Prop :=
  True

def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc

def append_postcond (a : Array Int) (b : Int) (result: Array Int) :=
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1

end VerinaSpec

namespace LLMSpec

-- No helper definitions are required.

def precondition (a : Array Int) (b : Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Int) (result : Array Int) : Prop :=
  result.size = a.size + 1 ∧
  (∀ (i : Nat), i < a.size → result[i]! = a[i]!) ∧
  result[a.size]! = b

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Int) : VerinaSpec.append_precond a b ↔ LLMSpec.precondition a b := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.append_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (b : Int) (result : Array Int) : LLMSpec.precondition a b →
  (VerinaSpec.append_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- By definition of VerinaSpec.append_postcond and LLMSpec.postcondition, we can see that they are equivalent by splitting into cases based on the preconditions.
  intros h_precond
  simp [VerinaSpec.append_postcond, LLMSpec.postcondition];
  -- The conjunction of three conditions is commutative, so the order of the conditions does not matter.
  simp [and_comm, and_assoc, and_left_comm]

end Proof