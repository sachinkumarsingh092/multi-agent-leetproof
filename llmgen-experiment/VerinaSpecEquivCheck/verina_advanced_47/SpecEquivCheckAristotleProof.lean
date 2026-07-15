/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ca54ff66-7334-4a72-af4f-865b93d161ca

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem precondition_equiv (intervals : List (Prod Int Int)) : VerinaSpec.mergeIntervals_precond intervals ↔ LLMSpec.precondition intervals

- theorem postcondition_equiv (intervals : List (Prod Int Int)) (result : List (Prod Int Int)) : LLMSpec.precondition intervals →
  (VerinaSpec.mergeIntervals_postcond intervals result ↔ LLMSpec.postcondition intervals result)

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

def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  True

def mergeIntervals_postcond (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) : Prop :=
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))
  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)
  covered ∧ noOverlap result

end VerinaSpec

namespace LLMSpec

-- An interval is represented as (start, end).
abbrev Interval := Prod Int Int

def intervalStart (iv : Interval) : Int := iv.1

def intervalEnd (iv : Interval) : Int := iv.2

-- Well-formed intervals have start ≤ end.
def intervalWellFormed (iv : Interval) : Prop :=
  intervalStart iv ≤ intervalEnd iv

-- Convert an Int endpoint to a rational point.
def intToRat (z : Int) : Rat :=
  Rat.ofInt z

-- Rational point membership in a closed interval.
def inIntervalRat (x : Rat) (iv : Interval) : Prop :=
  intToRat (intervalStart iv) ≤ x ∧ x ≤ intToRat (intervalEnd iv)

-- A rational point is covered by a list of intervals if it belongs to at least one interval.
def coversPointRat (intervals : List Interval) (x : Rat) : Prop :=
  ∃ (i : Nat), i < intervals.length ∧ inIntervalRat x (intervals[i]!)

-- List is sorted by nondecreasing start values.
def sortedByStart (intervals : List Interval) : Prop :=
  ∀ (i : Nat), i + 1 < intervals.length →
    intervalStart (intervals[i]!) ≤ intervalStart (intervals[i + 1]!)

-- Adjacent intervals are strictly separated: prev.end < next.start.
-- This forbids overlap and also forbids touching (since touching implies equality, not strict <).
def separatedAdjacent (intervals : List Interval) : Prop :=
  ∀ (i : Nat), i + 1 < intervals.length →
    intervalEnd (intervals[i]!) < intervalStart (intervals[i + 1]!)

-- All intervals in a list are well-formed.
def allWellFormed (intervals : List Interval) : Prop :=
  ∀ (i : Nat), i < intervals.length → intervalWellFormed (intervals[i]!)

-- Canonical-gap property: between any two consecutive output intervals, there exists a rational point
-- strictly between them that is not covered by the *input*.
-- This rules out gratuitous splitting of a continuously covered region.
def hasUncoveredGapWrtInput (input : List Interval) (result : List Interval) : Prop :=
  ∀ (i : Nat), i + 1 < result.length →
    ∃ (q : Rat),
      intToRat (intervalEnd (result[i]!)) < q ∧
      q < intToRat (intervalStart (result[i + 1]!)) ∧
      ¬ coversPointRat input q

-- Preconditions: input intervals are well-formed.
def precondition (intervals : List Interval) : Prop :=
  allWellFormed intervals

-- Postconditions:
-- 1) result intervals are well-formed
-- 2) result is sorted by start
-- 3) result intervals are strictly separated (no overlap)
-- 4) coverage equivalence over rational points (continuous interpretation)
-- 5) canonical-gap property with respect to the input (prevents non-canonical splitting)
def postcondition (intervals : List Interval) (result : List Interval) : Prop :=
  allWellFormed result ∧
  sortedByStart result ∧
  separatedAdjacent result ∧
  (∀ (x : Rat), coversPointRat intervals x ↔ coversPointRat result x) ∧
  hasUncoveredGapWrtInput intervals result

end LLMSpec

section Proof

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem precondition_equiv (intervals : List (Prod Int Int)) : VerinaSpec.mergeIntervals_precond intervals ↔ LLMSpec.precondition intervals := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any interval that is not well-formed.
  use [(1, 0)];
  -- Show that the interval [(1, 0)] is not well-formed.
  simp [VerinaSpec.mergeIntervals_precond, LLMSpec.precondition];
  -- Show that the interval (1, 0) is not well-formed.
  simp [LLMSpec.allWellFormed];
  -- Show that the interval (1, 0) is not well-formed by definition.
  unfold LLMSpec.intervalWellFormed
  simp [LLMSpec.intervalStart, LLMSpec.intervalEnd]

-/
theorem precondition_equiv (intervals : List (Prod Int Int)) : VerinaSpec.mergeIntervals_precond intervals ↔ LLMSpec.precondition intervals := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (intervals : List (Prod Int Int)) (result : List (Prod Int Int)) : LLMSpec.precondition intervals →
  (VerinaSpec.mergeIntervals_postcond intervals result ↔ LLMSpec.postcondition intervals result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the following example:
  use [(0, 1), (2, 3)], [(0, 3)];
  constructor;
  · -- Show that the intervals are well-formed.
    simp [LLMSpec.precondition, LLMSpec.intervalWellFormed];
    -- In this case, the list [(0, 1), (2, 3)] is well-formed since both intervals are well-formed.
    simp [LLMSpec.allWellFormed];
    simp +decide [ LLMSpec.intervalWellFormed ];
  · unfold LLMSpec.postcondition;
    unfold VerinaSpec.mergeIntervals_postcond LLMSpec.allWellFormed LLMSpec.sortedByStart LLMSpec.separatedAdjacent LLMSpec.hasUncoveredGapWrtInput LLMSpec.coversPointRat; simp +decide ;
    rintro -;
    use 1.5; norm_num [ LLMSpec.inIntervalRat ] ;
    native_decide +revert

-/
theorem postcondition_equiv (intervals : List (Prod Int Int)) (result : List (Prod Int Int)) : LLMSpec.precondition intervals →
  (VerinaSpec.mergeIntervals_postcond intervals result ↔ LLMSpec.postcondition intervals result) := by
  sorry

end Proof