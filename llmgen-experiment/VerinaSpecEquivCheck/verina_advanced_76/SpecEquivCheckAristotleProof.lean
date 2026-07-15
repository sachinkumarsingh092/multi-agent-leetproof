/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 19312cdc-8949-43b8-85cd-064db9cb6e45
To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
The following was proved by Aristotle:
- theorem precondition_equiv (nums : List Int) (k : Nat) : VerinaSpec.topKFrequent_precond nums k ↔ LLMSpec.precondition nums k
The following was negated by Aristotle:
- theorem postcondition_equiv (nums : List Int) (k : Nat) (result : List Int) : LLMSpec.precondition nums k →
  (VerinaSpec.topKFrequent_postcond nums k result ↔ LLMSpec.postcondition nums k result)
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
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) : Prop :=
  result.length = k ∧
  result.all (· ∈ nums) ∧
  List.Pairwise (· ≠ ·) result ∧
  (result.all (fun x =>
    nums.all (fun y =>
      y ∈ result ∨ nums.count x ≥ nums.count y
    ))) ∧
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x ≥ nums.count y
  ) result.zipIdx
end VerinaSpec
namespace LLMSpec
def freq (nums : List Int) (x : Int) : Nat :=
  nums.count x
def firstIndex (nums : List Int) (x : Int) : Nat :=
  match nums.findIdx? (fun y => y = x) with
  | some i => i
  | none => nums.length
def precedesByFreqThenFirst (nums : List Int) (a : Int) (b : Int) : Prop :=
  let fa := freq nums a
  let fb := freq nums b
  let ia := firstIndex nums a
  let ib := firstIndex nums b
  (fa > fb) ∨ (fa = fb ∧ ia < ib)
def isSortedByFreqThenFirst (nums : List Int) (xs : List Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < xs.length →
    precedesByFreqThenFirst nums xs[i]! xs[j]!
def precondition (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length
def postcondition (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∃ (sortedAll : List Int),
    sortedAll.Nodup ∧
    (∀ (x : Int), x ∈ sortedAll ↔ x ∈ nums) ∧
    isSortedByFreqThenFirst nums sortedAll ∧
    result = sortedAll.take k
end LLMSpec
section Proof
theorem precondition_equiv (nums : List Int) (k : Nat) : VerinaSpec.topKFrequent_precond nums k ↔ LLMSpec.precondition nums k := by
  -- The conditions are equivalent because they both state that k is less than or equal to the length of the list after removing duplicates.
  simp [VerinaSpec.topKFrequent_precond, LLMSpec.precondition]
/- Aristotle found this block to be false. Here is a proof of the negation:
noncomputable section AristotleLemmas
/-
Counterexample to the equivalence of postconditions: nums=[1, 2], k=1, result=[2]. VerinaSpec allows [2] (since freq 2 = freq 1), but LLMSpec requires [1] (due to index tie-breaking).
-/
theorem postcondition_equiv_counterexample :
  ∃ (nums : List Int) (k : Nat) (result : List Int),
    LLMSpec.precondition nums k ∧
    ¬ (VerinaSpec.topKFrequent_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  use [1, 2], 1, [2]
  constructor
  ·
    -- In this case, the length of the list [1, 2] is 2, which is greater than or equal to 1.
    simp [LLMSpec.precondition];
    decide +revert
  ·
    simp +decide [ VerinaSpec.topKFrequent_postcond, LLMSpec.postcondition ];
    intro x hx h'x h''x; rcases x with ( _ | ⟨ _, _ | ⟨ _, _ | x ⟩ ⟩ ) <;> simp_all +decide ;
    · cases h'x 1 ; cases h'x 2 ; aesop_cat;
    · have := h''x 0 1; simp_all +decide [ LLMSpec.precedesByFreqThenFirst ] ;
      cases h'x _ |>.2 ( Or.inl rfl ) ; cases h'x _ |>.2 ( Or.inr rfl ) ; aesop;
      · grind +ring;
      · cases h'x 1 ; cases h'x 2 ; aesop ( simp_config := { decide := true } ) ;
    · grind
end AristotleLemmas
theorem postcondition_equiv (nums : List Int) (k : Nat) (result : List Int) : LLMSpec.precondition nums k →
  (VerinaSpec.topKFrequent_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the counterexample to obtain the required `nums`, `k`, and `result`.
  obtain ⟨nums, k, result, h_pre, h_post⟩ := postcondition_equiv_counterexample;
  use nums, k, result;
  grind
-/
theorem postcondition_equiv (nums : List Int) (k : Nat) (result : List Int) : LLMSpec.precondition nums k →
  (VerinaSpec.topKFrequent_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  sorry
end Proof
