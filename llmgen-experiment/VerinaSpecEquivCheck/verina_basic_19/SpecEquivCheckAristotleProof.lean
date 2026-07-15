/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 046c6777-91f5-4b89-b4bc-75b26731f4cb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.isSorted_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.isSorted_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isSorted_precond (a : Array Int) : Prop :=
  True

def isSorted_postcond (a : Array Int) (result: Bool) :=
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result

end VerinaSpec

namespace LLMSpec

-- Adjacent non-decreasing property.
-- Uses Nat indices and the safe index operator a[i]! guarded by bounds.
def SortedAdjacent (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

def precondition (a : Array Int) : Prop :=
  True

-- The result is fully characterized:
-- result is true iff the adjacent sortedness predicate holds,
-- and result is false iff the adjacent sortedness predicate does not hold.
def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ SortedAdjacent a) ∧
  (result = false ↔ ¬ SortedAdjacent a)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.isSorted_precond a ↔ LLMSpec.precondition a := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.isSorted_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Bool) : LLMSpec.precondition a →
  (VerinaSpec.isSorted_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- By definition of `SortedAdjacent`, we know that if `SortedAdjacent a` holds, then `∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]`.
  have h_sorted_adjacent : LLMSpec.SortedAdjacent a ↔ (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) := by
    constructor <;> intro h i hi;
    · convert h i _;
      · exact?;
      · grind;
      · exact Nat.lt_pred_iff.mp hi;
    · grind;
  -- By definition of `postcondition`, we know that if `postcondition a result` holds, then `result` is true if and only if `SortedAdjacent a` holds, and `result` is false if and only if `¬SortedAdjacent a` holds.
  simp [LLMSpec.postcondition, h_sorted_adjacent];
  cases result <;> simp +decide [ VerinaSpec.isSorted_postcond ]

end Proof