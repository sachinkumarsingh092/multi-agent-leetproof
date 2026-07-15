/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f96cacba-2375-497e-9063-b76ee3c24ca5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (list : List Int) : VerinaSpec.mergeSort_precond list ↔ LLMSpec.precondition list

- theorem postcondition_equiv (list : List Int) (result : List Int) : LLMSpec.precondition list →
  (VerinaSpec.mergeSort_postcond list result ↔ LLMSpec.postcondition list result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def mergeSort_precond (list : List Int) : Prop :=
  True

def mergeSort_postcond (list : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm list result

end VerinaSpec

namespace LLMSpec

-- Preconditions: merge sort is defined for all lists of integers.
-- Note: SpecDSL requires the parameter binders of `precondition` and `postcondition`
-- to match exactly (same names/types/order).
def precondition (list : List Int) : Prop :=
  True

-- Postconditions:
-- 1) The result is sorted (ascending).
-- 2) The result contains exactly the same elements with the same multiplicities as the input,
--    expressed as equality of their coerced multisets.
def postcondition (list : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ ((result : Multiset Int) = (list : Multiset Int))

end LLMSpec

section Proof

theorem precondition_equiv (list : List Int) : VerinaSpec.mergeSort_precond list ↔ LLMSpec.precondition list := by
  -- Since both preconditions are trivially true, the equivalence is immediate.
  simp [VerinaSpec.mergeSort_precond, LLMSpec.precondition]

theorem postcondition_equiv (list : List Int) (result : List Int) : LLMSpec.precondition list →
  (VerinaSpec.mergeSort_postcond list result ↔ LLMSpec.postcondition list result) := by
  -- The postcondition for merge sort in the VerinaSpec is that the result is sorted and is a permutation of the input list. In the LLMSpec, the postcondition is that the result is sorted and that the multisets are equal.
  simp [VerinaSpec.mergeSort_postcond, LLMSpec.postcondition];
  -- The pairwise condition and the sorted condition are equivalent because a list is sorted if and only if it is pairwise less than or equal to itself.
  simp [List.Sorted, List.Pairwise];
  -- The equivalence follows directly from the definition of `List.isPerm`.
  simp [List.isPerm_iff];
  -- The equivalence follows directly from the symmetry of the permutation relation.
  intros h_pre h_sorted
  apply Iff.intro (fun h => h.symm) (fun h => h.symm)

end Proof