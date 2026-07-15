/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 120d5cd6-a319-4bd3-9aa5-0898955ed40b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Bool) : LLMSpec.precondition a b →
  (VerinaSpec.hasCommonElement_postcond a b result ↔ LLMSpec.postcondition a b result)

The following was negated by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.hasCommonElement_precond a b ↔ LLMSpec.precondition a b

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Mathlib.Tactic


namespace VerinaSpec

def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0

def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) :=
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result

end VerinaSpec

namespace LLMSpec

-- Helper predicate: there exists a value present in both arrays.
-- We use Array membership directly (no Array/List conversions in specs).
def hasCommon (a : Array Int) (b : Array Int) : Prop :=
  ∃ x : Int, x ∈ a ∧ x ∈ b

def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  (result = true ↔ hasCommon a b) ∧
  (result = false ↔ ¬ hasCommon a b)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.hasCommonElement_precond a b ↔ LLMSpec.precondition a b := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case where `a` and `b` are both empty.
  use #[], #[]
  simp [VerinaSpec.hasCommonElement_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.hasCommonElement_precond a b ↔ LLMSpec.precondition a b := by
  sorry

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Bool) : LLMSpec.precondition a b →
  (VerinaSpec.hasCommonElement_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  -- To prove the equivalence, we can show that the existence of indices i and j such that a[i]! equals b[j]! is equivalent to the existence of a value x that is in both a and b.
  have h_equiv : (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ ∃ x, x ∈ a ∧ x ∈ b := by
    constructor;
    · -- If there exist indices i and j such that i < a.size, j < b.size, and a[i]! = b[j]!, then a[i]! is in both a and b.
      intro h
      obtain ⟨i, j, hi, hj, h_eq⟩ := h
      use a[i]!;
      grind;
    · -- If there exists an element x in both a and b, then there must exist indices i and j such that a[i]! = x and b[j]! = x.
      intro hx
      obtain ⟨x, hx_a, hx_b⟩ := hx
      obtain ⟨i, hi⟩ : ∃ i, i < a.size ∧ a[i]! = x := by
        obtain ⟨ i, hi ⟩ := Array.mem_iff_getElem.mp hx_a; use i; aesop;
      obtain ⟨j, hj⟩ : ∃ j, j < b.size ∧ b[j]! = x := by
        obtain ⟨ j, hj ⟩ := Array.getElem_of_mem hx_b; use j; aesop;
      use i, j;
      grind;
  -- By combining the results from h_equiv and the definitions of the postconditions, we can conclude the equivalence.
  simp [VerinaSpec.hasCommonElement_postcond, LLMSpec.postcondition, h_equiv];
  cases result <;> simp_all +decide [ LLMSpec.hasCommon ]

end Proof