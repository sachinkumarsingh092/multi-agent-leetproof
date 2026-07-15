/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4d7d4536-f070-4e14-8aa7-58213ab03fe5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (l : List Int) : VerinaSpec.insertionSort_precond l ↔ LLMSpec.precondition l

- theorem postcondition_equiv (l : List Int) (result : List Int) : LLMSpec.precondition l →
  (VerinaSpec.insertionSort_postcond l result ↔ LLMSpec.postcondition l result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def insertionSort_precond (l : List Int) : Prop :=
  True

def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

def insertionSort_postcond (l : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result

end VerinaSpec

namespace LLMSpec

-- We use Mathlib's predicates:
-- * `l.Sorted (· ≤ ·)` for non-decreasing sortedness.
-- * `List.Perm` to express that two lists are permutations (same multiset of elements).

def precondition (l : List Int) : Prop :=
  True

def postcondition (l : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ List.Perm result l

end LLMSpec

section Proof

theorem precondition_equiv (l : List Int) : VerinaSpec.insertionSort_precond l ↔ LLMSpec.precondition l := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.insertionSort_precond, LLMSpec.precondition]

theorem postcondition_equiv (l : List Int) (result : List Int) : LLMSpec.precondition l →
  (VerinaSpec.insertionSort_postcond l result ↔ LLMSpec.postcondition l result) := by
  -- By definition of `insertionSort_postcond` and `postcondition`, we know that they are equivalent.
  simp [VerinaSpec.insertionSort_postcond, LLMSpec.postcondition];
  -- The equivalence follows directly from the definition of `List.Sorted` and `List.Perm`.
  simp [List.Sorted, List.Perm];
  -- By definition of `List.Perm`, we know that `l.isPerm result` is equivalent to `result.Perm l`.
  simp [List.isPerm_iff];
  grind

end Proof