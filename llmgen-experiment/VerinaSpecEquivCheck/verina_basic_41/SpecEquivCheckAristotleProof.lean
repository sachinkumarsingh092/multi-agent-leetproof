/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: db7548fb-2873-4936-b094-c90ca9171273

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.hasOnlyOneDistinctElement_postcond a result ↔ LLMSpec.postcondition a result)

The following was negated by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.hasOnlyOneDistinctElement_precond a ↔ LLMSpec.precondition a

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

def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  a.size > 0

def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) :=
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))

end VerinaSpec

namespace LLMSpec

-- Helper predicate: the array has at most one distinct value.
-- We make the empty-array case explicit to avoid out-of-bounds access to a[0]!. 
def allSame (a : Array Int) : Prop :=
  a.size = 0 ∨ (0 < a.size ∧ ∀ (i : Nat), i < a.size → a[i]! = a[0]!)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ allSame a) ∧
  (result = false ↔ ¬ allSame a)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (a : Array Int) : VerinaSpec.hasOnlyOneDistinctElement_precond a ↔ LLMSpec.precondition a := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the empty array.
  use #[]; simp [VerinaSpec.hasOnlyOneDistinctElement_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (a : Array Int) : VerinaSpec.hasOnlyOneDistinctElement_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.hasOnlyOneDistinctElement_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- Since both postconditions are equivalent to the array having only one distinct element, the implication holds.
  simp [VerinaSpec.hasOnlyOneDistinctElement_postcond, LLMSpec.postcondition, LLMSpec.allSame];
  rcases a with ⟨ ⟨ l ⟩ ⟩ <;> simp_all +decide [ List.pairwise_iff_get ];
  rcases result with ( _ | _ ) <;> simp_all +decide [ Fin.forall_fin_succ ];
  · -- Since the list is non-empty, the first element is indeed the head. Hence, the condition ¬(head✝ :: tail✝)[x] = head✝ can't be true for x = 0. Therefore, we can use x = 0 and show that it satisfies the condition.
    intros h_pre x hx h_neq
    use x
    aesop;
  · intro h; constructor <;> intro H <;> simp_all +decide [ Fin.forall_iff ] ;
    · grind +ring;
    · grind +ring

end Proof