/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fe59f500-862a-4802-8a5b-c1f4f70674ba

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (numbers : Array Int) (threshold : Int) : VerinaSpec.CountLessThan_precond numbers threshold ↔ LLMSpec.precondition numbers threshold

- theorem postcondition_equiv (numbers : Array Int) (threshold : Int) (result : Nat) : LLMSpec.precondition numbers threshold →
  (VerinaSpec.CountLessThan_postcond numbers threshold result ↔ LLMSpec.postcondition numbers threshold result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True

def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0

end VerinaSpec

namespace LLMSpec

-- We specify the count as the cardinality of the set of valid indices whose elements are < threshold.
-- This uses only standard Mathlib/Lean constructions: `Finset.range`, `Finset.filter`, and `Finset.card`.

def precondition (numbers : Array Int) (threshold : Int) : Prop :=
  True

def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) : Prop :=
  result = ((Finset.range numbers.size).filter (fun (i : Nat) => numbers[i]! < threshold)).card ∧
  result ≤ numbers.size

end LLMSpec

section Proof

theorem precondition_equiv (numbers : Array Int) (threshold : Int) : VerinaSpec.CountLessThan_precond numbers threshold ↔ LLMSpec.precondition numbers threshold := by
  -- Since both preconditions are defined as True, they are trivially equivalent.
  simp [VerinaSpec.CountLessThan_precond, LLMSpec.precondition]

theorem postcondition_equiv (numbers : Array Int) (threshold : Int) (result : Nat) : LLMSpec.precondition numbers threshold →
  (VerinaSpec.CountLessThan_postcond numbers threshold result ↔ LLMSpec.postcondition numbers threshold result) := by
  unfold VerinaSpec.CountLessThan_postcond LLMSpec.postcondition;
  -- By definition of `Array.foldl`, we can express it as a sum over the elements of the array.
  have h_foldl : Array.foldl (fun (count : ℕ) (n : ℤ) => if n < threshold then count + 1 else count) 0 numbers = Finset.sum (Finset.range numbers.size) (fun i => if numbers[i]! < threshold then 1 else 0) := by
    -- We can prove this by induction on the array's length.
    induction' numbers with n numbers ih;
    -- We can prove this by induction on the list `n`.
    induction' n with n ih;
    · rfl;
    · simp_all +decide [ Finset.sum_range_succ' ];
      rw [ Finset.card_filter ] at *;
      rw [ Finset.sum_range_succ' ];
      convert congr_arg ( fun x : ℕ => x + if n < threshold then 1 else 0 ) ‹List.foldl ( fun count n => if n < threshold then count + 1 else count ) 0 ih = ∑ i ∈ Finset.range ih.length, if ih[i]?.getD 0 < threshold then 1 else 0› using 1;
      clear ‹List.foldl ( fun count n => if n < threshold then count + 1 else count ) 0 ih = ∑ i ∈ Finset.range ih.length, if ih[i]?.getD 0 < threshold then 1 else 0›;
      induction ih using List.reverseRecOn <;> aesop;
  norm_num [ Finset.sum_ite ] at *;
  grind

end Proof