/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 15b0da7d-a743-4bee-8f67-660c9e748a8c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int) : VerinaSpec.firstDuplicate_precond lst ↔ LLMSpec.precondition lst

The following was negated by Aristotle:

- theorem postcondition_equiv (lst : List Int) (result : Option Int) : LLMSpec.precondition lst →
  (VerinaSpec.firstDuplicate_postcond lst result ↔ LLMSpec.postcondition lst result)

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

def firstDuplicate_precond (lst : List Int) : Prop :=
  True

def firstDuplicate_postcond (lst : List Int) (result: Option Int) : Prop :=
  match result with
  | none => List.Nodup lst
  | some x =>
    lst.count x > 1 ∧
    (lst.filter (fun y => lst.count y > 1)).head? = some x

end VerinaSpec

namespace LLMSpec

-- Helper: j is a duplicate occurrence if the element at j appears earlier.
-- We include j < lst.length so that all indexing operations are safe.
def DupAt (lst : List Int) (j : Nat) : Prop :=
  j < lst.length ∧ ∃ i : Nat, i < j ∧ lst[i]! = lst[j]!

-- Helper: j is the first index (smallest) that is a duplicate occurrence.
def IsFirstDupIndex (lst : List Int) (j : Nat) : Prop :=
  DupAt lst j ∧ ∀ k : Nat, k < j → ¬ DupAt lst k

-- No input restrictions.
def precondition (lst : List Int) : Prop :=
  True

def postcondition (lst : List Int) (result : Option Int) : Prop :=
  match result with
  | none =>
      -- No position is a duplicate occurrence.
      ∀ j : Nat, j < lst.length → ¬ DupAt lst j
  | some x =>
      -- There is a first duplicate index j, and x is the value at that position.
      ∃ j : Nat, IsFirstDupIndex lst j ∧ lst[j]! = x

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) : VerinaSpec.firstDuplicate_precond lst ↔ LLMSpec.precondition lst := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.firstDuplicate_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Disproof of the equivalence by counterexample: [1, 2, 2, 1] with result (some 1). VerinaSpec accepts this (first element with count > 1 is 1), but LLMSpec rejects it (first duplicate index is 2, value 2).
-/
lemma counterexample_disproof : ∃ lst result, VerinaSpec.firstDuplicate_postcond lst result ∧ ¬ LLMSpec.postcondition lst result := by
  unfold LLMSpec.postcondition VerinaSpec.firstDuplicate_postcond;
  use [ 1, 2, 2, 1 ];
  use Option.some 1; simp +decide ;
  rintro ( x | x | x | x | x ) <;> simp +decide [ LLMSpec.IsFirstDupIndex ];
  · simp +decide [ LLMSpec.DupAt ];
  · simp +decide [ LLMSpec.DupAt ]

end AristotleLemmas

theorem postcondition_equiv (lst : List Int) (result : Option Int) : LLMSpec.precondition lst →
  (VerinaSpec.firstDuplicate_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Use the counterexample_disproof lemma to obtain the list and result.
  obtain ⟨lst, result, h_valid, h_contradiction⟩ := counterexample_disproof;
  use lst, result;
  -- Since the precondition is True, we can conclude the proof.
  simp [h_contradiction, h_valid];
  -- Since the precondition is True, we can conclude the proof by using the fact that True is true.
  simp [LLMSpec.precondition]

-/
theorem postcondition_equiv (lst : List Int) (result : Option Int) : LLMSpec.precondition lst →
  (VerinaSpec.firstDuplicate_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  sorry

end Proof