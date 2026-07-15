/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3c352548-29ef-4c6e-b129-be7fe9a78838

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (arr : Array Int) (k : Int) : VerinaSpec.maxSubarraySumDivisibleByK_precond arr k ↔ LLMSpec.precondition arr k

- theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Int) : LLMSpec.precondition arr k →
  (VerinaSpec.maxSubarraySumDivisibleByK_postcond arr k result ↔ LLMSpec.postcondition arr k result)

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

def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  k > 0

def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k.toNat = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.toList.sum)
  (subarraySums.length = 0 → result = 0) ∧
  (subarraySums.length > 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))

end VerinaSpec

namespace LLMSpec

-- Convert the (positive) Int k to Nat for divisibility over Nat lengths.
-- Precondition guarantees 2 ≤ k, so Int.toNat k is nonzero.
def kNat (k : Int) : Nat :=
  Int.toNat k

-- Sum of the subarray arr[start:stop] (stop exclusive).
-- We use Array.extract, together with explicit bounds in predicates, to model a subarray slice.
def subarraySum (arr : Array Int) (start : Nat) (stop : Nat) : Int :=
  (arr.extract start stop).sum

-- A non-empty, in-bounds subarray.
def validSubarray (arr : Array Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ arr.size

-- Length divisibility by k (with k viewed as a natural number).
def lenDivisibleByK (len : Nat) (k : Int) : Prop :=
  len % (kNat k) = 0

-- Candidate predicate: a valid non-empty subarray with length divisible by k.
def isCandidate (arr : Array Int) (k : Int) (start : Nat) (stop : Nat) : Prop :=
  validSubarray arr start stop ∧ lenDivisibleByK (stop - start) k

-- k must be larger than 1.
def precondition (arr : Array Int) (k : Int) : Prop :=
  2 ≤ k

-- result is the greatest nonnegative sum among all candidate subarrays; default 0.
def postcondition (arr : Array Int) (k : Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∀ (start : Nat) (stop : Nat), isCandidate arr k start stop → subarraySum arr start stop ≤ result) ∧
  (result = 0 ∨ ∃ (start : Nat) (stop : Nat), isCandidate arr k start stop ∧ subarraySum arr start stop = result)

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (arr : Array Int) (k : Int) : VerinaSpec.maxSubarraySumDivisibleByK_precond arr k ↔ LLMSpec.precondition arr k := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $k$ such that $1 \leq k \leq 1$.
  use #[1], 1
  simp [VerinaSpec.maxSubarraySumDivisibleByK_precond, LLMSpec.precondition]

-/
theorem precondition_equiv (arr : Array Int) (k : Int) : VerinaSpec.maxSubarraySumDivisibleByK_precond arr k ↔ LLMSpec.precondition arr k := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Int) : LLMSpec.precondition arr k →
  (VerinaSpec.maxSubarraySumDivisibleByK_postcond arr k result ↔ LLMSpec.postcondition arr k result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  fconstructor;
  exact #[-1, -2];
  use 2; simp +decide [ LLMSpec.precondition ] ;
  -- Let's choose the result to be -3.
  use -3; simp +decide [VerinaSpec.maxSubarraySumDivisibleByK_postcond, LLMSpec.postcondition]

-/
theorem postcondition_equiv (arr : Array Int) (k : Int) (result : Int) : LLMSpec.precondition arr k →
  (VerinaSpec.maxSubarraySumDivisibleByK_postcond arr k result ↔ LLMSpec.postcondition arr k result) := by
  sorry

end Proof