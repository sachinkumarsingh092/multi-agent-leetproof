/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b71bc4a0-6d8c-46e2-8981-c1682abb084c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (operations : List Int) : VerinaSpec.below_zero_precond operations ↔ LLMSpec.precondition operations

- theorem postcondition_equiv (operations : List Int) (result : (Array Int × Bool)) : LLMSpec.precondition operations →
  (VerinaSpec.below_zero_postcond operations result ↔ LLMSpec.postcondition operations result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def below_zero_precond (operations : List Int) : Prop :=
  True

def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))

end VerinaSpec

namespace LLMSpec

-- Helper: interpret a partial sum at index i as the sum of the first i operations.
-- We rely on Mathlib/Init definitions: List.take and List.sum.

def precondition (operations : List Int) : Prop :=
  True

def postcondition (operations : List Int) (result : (Array Int × Bool)) : Prop :=
  let ps : Array Int := result.1
  let neg : Bool := result.2
  -- Shape of the partial-sum array
  ps.size = operations.length + 1 ∧
  -- Each position i contains the sum of the first i operations
  (∀ (i : Nat), i < ps.size → ps[i]! = (operations.take i).sum) ∧
  -- Negativity flag: some partial sum after index 0 is negative
  (neg = true ↔ ∃ (i : Nat), i < ps.size ∧ i ≠ 0 ∧ ps[i]! < 0)

end LLMSpec

section Proof

theorem precondition_equiv (operations : List Int) : VerinaSpec.below_zero_precond operations ↔ LLMSpec.precondition operations := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.below_zero_precond, LLMSpec.precondition]

theorem postcondition_equiv (operations : List Int) (result : (Array Int × Bool)) : LLMSpec.precondition operations →
  (VerinaSpec.below_zero_postcond operations result ↔ LLMSpec.postcondition operations result) := by
  rintro -;
  constructor <;> intro h;
  · -- By definition of `VerinaSpec.below_zero_postcond`, we know that `s` is the array of partial sums of `operations`.
    obtain ⟨s, hs⟩ := h;
    refine' ⟨ s, _, _ ⟩ <;> simp_all +decide [ List.range_succ_eq_map ];
    · intro i hi; induction' i with i ih <;> simp_all +decide [ List.take_succ ] ;
      grind;
    · grind;
  · -- By definition of LLMSpec.postcondition, we know that the partial sums array is correctly built and the negativity flag is set based on the presence of negative partial sums.
    obtain ⟨h_size, h_partial_sums, h_neg⟩ := h;
    refine' ⟨ h_size, _, _, _, _ ⟩;
    · grind;
    · simp_all +decide [ List.range_succ ];
      grind;
    · -- If result.2 is true, then there exists some i in the range of operations.length such that result.1[i + 1]! is negative.
      intro h_true
      obtain ⟨i, hi₁, hi₂, hi₃⟩ := h_neg.mp h_true;
      rcases i <;> aesop;
    · grind

end Proof