/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4cba7c92-2f08-4263-a2b1-66049404ba3a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) : LLMSpec.precondition nums k →
  (VerinaSpec.minOperations_postcond nums k result ↔ LLMSpec.postcondition nums k result)

The following was negated by Aristotle:

- theorem precondition_equiv (nums : List Nat) (k : Nat) : VerinaSpec.minOperations_precond nums k ↔ LLMSpec.precondition nums k

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

def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)

def minOperations_postcond (nums : List Nat) (k : Nat) (result: Nat) : Prop :=
  let processed := (nums.reverse).take result
  let target_nums := (List.range k).map (· + 1)
  let collected_all := target_nums.all (fun n => List.elem n processed)
  let is_minimal :=
    if result > 0 then
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      k == 0
  collected_all ∧ is_minimal

end VerinaSpec

namespace LLMSpec

-- The sublist consisting of the last `r` elements of `nums`.
-- This is exactly the multiset of elements collected after performing `r` removals from the end.
def collectedSuffix (nums : List Nat) (r : Nat) : List Nat :=
  nums.drop (nums.length - r)

-- All numbers in the range 1..k appear in the collected suffix.
def coversRange (nums : List Nat) (k : Nat) (r : Nat) : Prop :=
  ∀ (t : Nat), 1 ≤ t → t ≤ k → t ∈ collectedSuffix nums r

-- Preconditions:
-- 1) k is positive
-- 2) nums contains all integers from 1..k
-- Note: We do not require nums elements to be > 0 explicitly since Nat already enforces non-negativity,
-- and the main required domain constraint is that 1..k are present.
def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0 ∧
  (∀ (t : Nat), 1 ≤ t → t ≤ k → t ∈ nums)

-- Postcondition:
-- result is a valid number of removals (≤ length)
-- the last `result` elements cover 1..k
-- and `result` is minimal with that property.
def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=
  result ≤ nums.length ∧
  coversRange nums k result ∧
  (∀ (r' : Nat), r' < result → ¬ coversRange nums k r')

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (nums : List Nat) (k : Nat) : VerinaSpec.minOperations_precond nums k ↔ LLMSpec.precondition nums k := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the case when `k` is zero.
  use [], 0
  simp [VerinaSpec.minOperations_precond, LLMSpec.precondition] at *

-/
theorem precondition_equiv (nums : List Nat) (k : Nat) : VerinaSpec.minOperations_precond nums k ↔ LLMSpec.precondition nums k := by
  sorry

theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) : LLMSpec.precondition nums k →
  (VerinaSpec.minOperations_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  unfold LLMSpec.precondition VerinaSpec.minOperations_postcond LLMSpec.postcondition;
  -- To prove the equivalence, we can show that the collected suffix in the LLMSpec is the same as the processed list in the VerinaSpec when reversed.
  have h_collected_suffix : ∀ r, LLMSpec.coversRange nums k r ↔ (List.map (fun x => x + 1) (List.range k)).all (fun n => List.elem n (List.take r (List.reverse nums))) := by
    -- To prove the equivalence, we can show that the collected suffix in the LLMSpec is the same as the processed list in the VerinaSpec when reversed. This follows from the fact that reversing the list and taking the first r elements is equivalent to taking the last r elements of the original list.
    intros r
    simp [LLMSpec.coversRange, List.take_reverse];
    exact ⟨ fun h x hx => h _ ( Nat.succ_pos _ ) ( Nat.succ_le_of_lt hx ), fun h x hx₁ hx₂ => h ( x - 1 ) ( by omega ) |> fun h' => by cases x <;> aesop ⟩;
  rcases result with ( _ | result ) <;> simp_all +decide;
  · exact fun hk₁ hk₂ hk₃ => absurd ( hk₃ 0 ) ( by linarith );
  · intro hk hnums
    constructor
    intro h
    obtain ⟨hx1, hx2⟩ := h
    have h_length : result + 1 ≤ nums.length := by
      have := hx1 0 hk; simp_all +decide [ List.take_reverse ] ;
      grind
    have h_minimal : ∀ r' < result + 1, ∃ x < k, x + 1 ∉ List.take r' nums.reverse := by
      intros r' hr';
      contrapose! hx2;
      -- Since $r' < result + 1$, the take of $r'$ elements is a subset of the take of $result$ elements.
      have h_subset : List.take r' nums.reverse ⊆ List.take result nums.reverse := by
        -- Since $r' < result + 1$, the list taken up to $r'$ is a prefix of the list taken up to $result$.
        have h_prefix : List.take r' nums.reverse = List.take r' (List.take result nums.reverse) := by
          grind;
        exact h_prefix.symm ▸ List.take_subset _ _;
      exact fun x hx => h_subset ( hx2 x hx )
    exact ⟨h_length, hx1, h_minimal⟩
    intro h
    obtain ⟨h_length, hx1, hx2⟩ := h
    have h_exists : ∃ x < k, x + 1 ∉ List.take result nums.reverse := by
      exact hx2 _ ( Nat.lt_succ_self _ )
    exact ⟨hx1, h_exists⟩

end Proof