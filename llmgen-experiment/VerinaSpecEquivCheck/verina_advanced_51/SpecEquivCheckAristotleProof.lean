/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7a1fab01-10e7-4223-9f3b-3fae8cb9a027

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : List Int) (b : List Int) : VerinaSpec.mergeSorted_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : List Int) (b : List Int) (result : List Int) : LLMSpec.precondition a b →
  (VerinaSpec.mergeSorted_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b

def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged

def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)

end VerinaSpec

namespace LLMSpec

-- Helper: non-decreasing sortedness for Int lists.
-- Mathlib provides `List.Sorted`.
def sortedND (l : List Int) : Prop :=
  l.Sorted (fun x y => x ≤ y)

-- Precondition: both input lists are sorted in non-decreasing order.
def precondition (a : List Int) (b : List Int) : Prop :=
  sortedND a ∧ sortedND b

-- Postcondition:
-- 1) result is sorted in non-decreasing order
-- 2) result contains exactly all elements from a and b, counting duplicates
-- 3) result length equals sum of input lengths
-- Note: we avoid `List.toMultiset` (not available in this environment) and instead
-- specify multiplicities using `List.count`.
def postcondition (a : List Int) (b : List Int) (result : List Int) : Prop :=
  sortedND result ∧
  (∀ x : Int, result.count x = a.count x + b.count x) ∧
  result.length = a.length + b.length

end LLMSpec

section Proof

theorem precondition_equiv (a : List Int) (b : List Int) : VerinaSpec.mergeSorted_precond a b ↔ LLMSpec.precondition a b := by
  -- The equivalence follows directly from the definitions of `VerinaSpec.mergeSorted_precond` and `LLMSpec.precondition`.
  simp [VerinaSpec.mergeSorted_precond, LLMSpec.precondition, List.Pairwise, List.Sorted];
  -- The equivalence follows directly from the definitions of `VerinaSpec.mergeSorted_precond` and `LLMSpec.precondition` since `List.Pairwise (· ≤ ·)` is equivalent to `List.Sorted (· ≤ ·)`.
  simp [LLMSpec.sortedND];
  -- The equivalence follows directly from the definitions of `List.Pairwise` and `List.Sorted`.
  simp [List.Pairwise, List.Sorted]

theorem postcondition_equiv (a : List Int) (b : List Int) (result : List Int) : LLMSpec.precondition a b →
  (VerinaSpec.mergeSorted_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  unfold VerinaSpec.mergeSorted_postcond LLMSpec.postcondition LLMSpec.precondition;
  simp +decide [ LLMSpec.sortedND, List.isPerm_iff ];
  intro ha hb; constructor <;> intro h <;> simp_all +decide [ List.Sorted ] ;
  · exact ⟨ fun x => by rw [ h.2.count_eq, List.count_append ], by rw [ h.2.length_eq, List.length_append ] ⟩;
  · rw [ List.perm_iff_count ] ; aesop;

end Proof