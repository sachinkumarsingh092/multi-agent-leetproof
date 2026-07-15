/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bd65edc2-f869-41cc-b471-51373561df89

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (e : Int) : VerinaSpec.LinearSearch_precond a e ↔ LLMSpec.precondition a e

- theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) : LLMSpec.precondition a e →
  (VerinaSpec.LinearSearch_postcond a e result ↔ LLMSpec.postcondition a e result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e

def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)

end VerinaSpec

namespace LLMSpec

-- `e` must occur in `a` at some in-bounds index.
def precondition (a : Array Int) (e : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = e

-- `result` is an in-bounds index of the first occurrence of `e`.
def postcondition (a : Array Int) (e : Int) (result : Nat) : Prop :=
  result < a.size ∧
  a[result]! = e ∧
  (∀ j : Nat, j < a.size → j < result → a[j]! ≠ e)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (e : Int) : VerinaSpec.LinearSearch_precond a e ↔ LLMSpec.precondition a e := by
  -- The two conditions are identical, so the equivalence holds trivially.
  simp [VerinaSpec.LinearSearch_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (e : Int) (result : Nat) : LLMSpec.precondition a e →
  (VerinaSpec.LinearSearch_postcond a e result ↔ LLMSpec.postcondition a e result) := by
  -- By definition of `LinearSearch_postcond` and `postcondition`, we can show that they are equivalent under the given preconditions.
  intros h_pre
  simp [VerinaSpec.LinearSearch_postcond, LLMSpec.postcondition];
  grind

end Proof