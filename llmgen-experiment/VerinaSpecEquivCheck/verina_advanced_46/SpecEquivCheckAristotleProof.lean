/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 48ff3b66-377b-4eed-ba43-a89c31a5d80d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (numbers : List Int) : VerinaSpec.maxSubarraySum_precond numbers ↔ LLMSpec.precondition numbers

- theorem postcondition_equiv (numbers : List Int) (result : Int) : LLMSpec.precondition numbers →
  (VerinaSpec.maxSubarraySum_postcond numbers result ↔ LLMSpec.postcondition numbers result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def maxSubarraySum_precond (numbers : List Int) : Prop :=
  True

def maxSubarraySum_postcond (numbers : List Int) (result: Int) : Prop :=
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- Sum of a list slice determined by `start` and `len`.
-- The slice is `(numbers.drop start).take len`.
-- Using `List.sum` is a declarative characterization of the slice sum.
-- (It is still computable, but does not commit to a particular traversal strategy.)
def sliceSum (numbers : List Int) (start : Nat) (len : Nat) : Int :=
  ((numbers.drop start).take len).sum

-- A slice is valid if it does not extend past the end of the list.
def validSlice (numbers : List Int) (start : Nat) (len : Nat) : Prop :=
  start + len ≤ numbers.length

-- Preconditions: none.
def precondition (numbers : List Int) : Prop :=
  True

-- Postcondition: `result` is the maximum slice sum among all valid contiguous slices,
-- with the empty slice permitted.
--
-- Characterization:
-- 1) Nonnegativity (because the empty slice has sum 0).
-- 2) Upper bound: every valid slice sum is ≤ result.
-- 3) Achievability: some valid slice attains result.
def postcondition (numbers : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∀ (start : Nat) (len : Nat), validSlice numbers start len → sliceSum numbers start len ≤ result) ∧
  (∃ (start : Nat) (len : Nat), validSlice numbers start len ∧ sliceSum numbers start len = result)

end LLMSpec

section Proof

theorem precondition_equiv (numbers : List Int) : VerinaSpec.maxSubarraySum_precond numbers ↔ LLMSpec.precondition numbers := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.maxSubarraySum_precond, LLMSpec.precondition]

theorem postcondition_equiv (numbers : List Int) (result : Int) : LLMSpec.precondition numbers →
  (VerinaSpec.maxSubarraySum_postcond numbers result ↔ LLMSpec.postcondition numbers result) := by
  unfold LLMSpec.postcondition VerinaSpec.maxSubarraySum_postcond;
  unfold LLMSpec.validSlice LLMSpec.sliceSum;
  simp +zetaDelta at *;
  refine' fun _ => ⟨ fun h => ⟨ _, _, _ ⟩, fun h => ⟨ _, _ ⟩ ⟩;
  · exact h.2 0 ( Nat.zero_lt_succ _ ) 0 ( Nat.zero_lt_succ _ ) |> le_trans ( by norm_num );
  · exact fun start len h' => h.2 start ( by linarith ) len ( by omega );
  · grind;
  · obtain ⟨ start, len, h₁, h₂ ⟩ := h.2.2; exact ⟨ start, by linarith, len, by omega, h₂ ⟩ ;
  · exact fun x hx y hy => h.2.1 x y ( by omega )

end Proof