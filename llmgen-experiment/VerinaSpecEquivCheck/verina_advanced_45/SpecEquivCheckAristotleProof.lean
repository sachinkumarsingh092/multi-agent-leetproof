/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 58f898eb-eba9-475d-b44e-904088fa29aa

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) : VerinaSpec.maxSubarraySum_precond xs ↔ LLMSpec.precondition xs

The following was negated by Aristotle:

- theorem postcondition_equiv (xs : List Int) (result : Int) : LLMSpec.precondition xs →
  (VerinaSpec.maxSubarraySum_postcond xs result ↔ LLMSpec.postcondition xs result)

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

def maxSubarraySum_precond (xs : List Int) : Prop :=
  True

def maxSubarraySum_postcond (xs : List Int) (result: Int) : Prop :=
  let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start =>
    List.range' 1 (xs.length - start) |>.map (fun len =>
      ((xs.drop start).take len).sum
    ))
  let has_result_subarray := subarray_sums.any (fun sum => sum == result)
  let is_maximum := subarray_sums.all (· ≤ result)
  match xs with
  | [] => result == 0
  | _ => has_result_subarray ∧ is_maximum

end VerinaSpec

namespace LLMSpec

-- Sum of the subarray xs[i..j) (start inclusive, end exclusive).
-- This includes the empty subarray when i = j, whose sum is 0.
-- Indices are Nat; bounds are enforced in the postcondition.
def subarraySum (xs : List Int) (i : Nat) (j : Nat) : Int :=
  ((xs.drop i).take (j - i)).sum

def precondition (xs : List Int) : Prop :=
  True

-- The result is a maximum among all subarray sums (including empty subarrays),
-- and is achievable by some valid indices.
def postcondition (xs : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ (i : Nat) (j : Nat), i ≤ j ∧ j ≤ xs.length ∧ subarraySum xs i j = result) ∧
  (∀ (i : Nat) (j : Nat), i ≤ j ∧ j ≤ xs.length → subarraySum xs i j ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) : VerinaSpec.maxSubarraySum_precond xs ↔ LLMSpec.precondition xs := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.maxSubarraySum_precond, LLMSpec.precondition]

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (xs : List Int) (result : Int) : LLMSpec.precondition xs →
  (VerinaSpec.maxSubarraySum_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the list $xs = [-1, -2, -3]$.
  use [-1, -2, -3];
  -- Let's simplify the goal.
  simp [VerinaSpec.maxSubarraySum_postcond, LLMSpec.postcondition];
  -- Let's choose the result to be -1.
  use by
    -- The precondition is trivially satisfied for any list.
    simp [LLMSpec.precondition]
  use -1
  simp +decide [ LLMSpec.subarraySum ];
  -- Let's choose $x = 0$ and $x_1 = 1$.
  use 0, by norm_num, 1, by norm_num
  simp [List.take, List.drop]

-/
theorem postcondition_equiv (xs : List Int) (result : Int) : LLMSpec.precondition xs →
  (VerinaSpec.maxSubarraySum_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  sorry

end Proof