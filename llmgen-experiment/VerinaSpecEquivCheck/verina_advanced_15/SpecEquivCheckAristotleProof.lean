/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 56bfe178-d4b0-4db2-b823-2036082e0226

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.increasingTriplet_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Bool) : LLMSpec.precondition nums →
  (VerinaSpec.increasingTriplet_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def increasingTriplet_precond (nums : List Int) : Prop :=
  True

def increasingTriplet_postcond (nums : List Int) (result: Bool) : Prop :=
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))

end VerinaSpec

namespace LLMSpec

-- There exists a strictly increasing subsequence of length 3, witnessed by indices i<j<k.
-- We use `nums[i]!` with an explicit bound `k < nums.length` to ensure all accesses are in range.
def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ (i : Nat) (j : Nat) (k : Nat),
    i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!

def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Bool) : Prop :=
  result = true ↔ hasIncreasingTriplet nums

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.increasingTriplet_precond nums ↔ LLMSpec.precondition nums := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.increasingTriplet_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Bool) : LLMSpec.precondition nums →
  (VerinaSpec.increasingTriplet_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold LLMSpec.postcondition VerinaSpec.increasingTriplet_postcond LLMSpec.precondition;
  -- To prove the equivalence, we can use the definitions of the postconditions to split into cases based on the value of `result`.
  by_cases h : result = Bool.true <;> simp [h];
  · -- To prove the equivalence, we can use the definitions of the postconditions to split into cases based on the value of `result`. Since `result` is true, we need to show that the existence of a triplet in the zipped list implies the existence of a triplet in the original list, and vice versa.
    apply Iff.intro;
    · rintro ⟨ a, b, h₁, c, d, h₂, e, f, h₃, h₄, h₅, h₆ ⟩;
      use b, d, f;
      grind;
    · rintro ⟨ i, j, k, hij, hjk, hk, hi, hj ⟩ ; use nums[i]!, i, by
        grind, nums[j]!, j, by
        grind, nums[k]!, k, by
        grind ;
  · constructor <;> intro h';
    · contrapose! h';
      rcases h' with ⟨ i, j, k, hij, hjk, hk, hi, hj ⟩ ; use nums[i]!, i, ?_, nums[j]!, j, ?_, nums[k]!, k, ?_ <;> simp_all +decide [ List.getElem?_eq_getElem ] ;
      · grind;
      · grind;
      · grind;
    · contrapose! h';
      obtain ⟨ a, b, h₁, c, d, h₂, e, f, h₃, h₄, h₅, h₆ ⟩ := h';
      use b, d, f;
      grind

end Proof