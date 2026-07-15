/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f466b250-2830-419c-82c8-a3f902fde87d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a1 : Array Nat) (a2 : Array Nat) : VerinaSpec.mergeSorted_precond a1 a2 ↔ LLMSpec.precondition a1 a2

The following was negated by Aristotle:

- theorem postcondition_equiv (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : LLMSpec.precondition a1 a2 →
  (VerinaSpec.mergeSorted_postcond a1 a2 result ↔ LLMSpec.postcondition a1 a2 result)

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

def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList

def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)

end VerinaSpec

namespace LLMSpec

-- Helper: element membership in an array, expressed via index-based access.
-- (Avoids Array/List conversions in specifications.)
def inArray (arr : Array Nat) (x : Nat) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: sortedness for arrays (nondecreasing).
def isSorted (arr : Array Nat) : Prop :=
  ∀ (i : Nat), i + 1 < arr.size → arr[i]! ≤ arr[i + 1]!

-- Helper: no duplicates in an array (index-based extensional nodup).
def nodupArray (arr : Array Nat) : Prop :=
  ∀ (i : Nat) (j : Nat),
    i < arr.size → j < arr.size → arr[i]! = arr[j]! → i = j

-- Preconditions: both arrays are sorted (nondecreasing). Behavior is unspecified otherwise.
def precondition (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  isSorted a1 ∧ isSorted a2

-- Postconditions:
-- 1. result is sorted
-- 2. result has no duplicates
-- 3. membership in result is exactly union of memberships of a1 and a2
-- Together these characterize the unique sorted duplicate-free representation of the union.
def postcondition (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  isSorted result ∧
  nodupArray result ∧
  (∀ (x : Nat), inArray result x ↔ (inArray a1 x ∨ inArray a2 x))

end LLMSpec

section Proof

theorem precondition_equiv (a1 : Array Nat) (a2 : Array Nat) : VerinaSpec.mergeSorted_precond a1 a2 ↔ LLMSpec.precondition a1 a2 := by
  -- The pairwise condition for a list is equivalent to the sortedness condition for an array.
  have h_pairwise_sorted : ∀ (l : List ℕ), List.Pairwise (· ≤ ·) l ↔ ∀ i, i + 1 < l.length → l[i]! ≤ l[i + 1]! := by
    intro l;
    constructor <;> intro h <;> rw [ List.pairwise_iff_get ] at *;
    · -- By definition of pairwise condition, if i < j, then l[i] ≤ l[j].
      intros i hi
      specialize h ⟨i, by linarith⟩ ⟨i + 1, by linarith⟩ (Nat.lt_succ_self i);
      grind +ring;
    · intro i j hij;
      -- By induction on $j - i$, we can show that $l.get i \leq l.get j$ for any $i < j$.
      induction' j with j ih generalizing i;
      induction' j with j ih generalizing i;
      · tauto;
      · grind;
  -- Apply the equivalence of pairwise sortedness and sortedness for lists to both a1 and a2.
  simp [VerinaSpec.mergeSorted_precond, LLMSpec.precondition, h_pairwise_sorted];
  -- The equivalence follows directly from the definition of `isSorted`.
  simp [LLMSpec.isSorted];
  grind +ring

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem postcondition_equiv (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : LLMSpec.precondition a1 a2 →
  (VerinaSpec.mergeSorted_postcond a1 a2 result ↔ LLMSpec.postcondition a1 a2 result) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the following example:
  use #[1, 1, 2], #[1, 2, 2];
  -- Let's choose the result array to be `[1, 1, 1, 2, 2, 2]`.
  use #[1, 1, 1, 2, 2, 2];
  constructor;
  · constructor <;> intro i hi <;> rcases i with ( _ | _ | i ) <;> trivial;
  · unfold VerinaSpec.mergeSorted_postcond LLMSpec.postcondition; simp +decide ;
    intro h1 h2; specialize h2 0 1; simp_all +decide ;

-/
theorem postcondition_equiv (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : LLMSpec.precondition a1 a2 →
  (VerinaSpec.mergeSorted_postcond a1 a2 result ↔ LLMSpec.postcondition a1 a2 result) := by
  sorry

end Proof