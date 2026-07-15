/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e751a15b-7c52-4cc3-b4ef-8811dbfe972d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.majorityElement_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.majorityElement_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def majorityElement_precond (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)

-- majority element must exist

def majorityElement_postcond (nums : List Int) (result: Int) : Prop :=
  let n := nums.length
  (List.count result nums > n / 2) ∧
  nums.all (fun x => x = result ∨ List.count x nums ≤ n / 2)

end VerinaSpec

namespace LLMSpec

-- A predicate characterizing when a value is a majority element of a list.
-- We use `List.count` (with `BEq Int`) to count occurrences.
def IsMajority (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2

-- Precondition: a majority element exists.
-- Note: This implies `nums` is nonempty.
def precondition (nums : List Int) : Prop :=
  ∃ x : Int, IsMajority nums x

-- Postcondition: the result is a majority element, and it is the unique such value.
def postcondition (nums : List Int) (result : Int) : Prop :=
  IsMajority nums result ∧
  (∀ x : Int, IsMajority nums x → x = result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.majorityElement_precond nums ↔ LLMSpec.precondition nums := by
  -- The two preconditions are equivalent because they both assert the existence of a majority element.
  simp [VerinaSpec.majorityElement_precond, LLMSpec.precondition];
  constructor <;> intro a;
  · -- Since `a` already gives us such an `x`, we can use it directly.
    obtain ⟨x, hx⟩ := a.right;
    use x;
    aesop;
  · obtain ⟨ x, hx ⟩ := a;
    exact ⟨ List.length_pos_iff.mpr ( by rintro rfl; contradiction ), x, List.count_pos_iff.mp ( pos_of_gt hx ), hx ⟩

theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.majorityElement_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  -- If the Verina postcondition holds, then result is a majority element, and for any x, if x's count is greater than half the length, then x must be the same as result. Therefore, the result in the Verina postcondition must be the unique majority element.
  intro h_pre
  simp [VerinaSpec.majorityElement_postcond, LLMSpec.postcondition];
  constructor <;> intro h <;> unfold LLMSpec.IsMajority at * <;> simp_all +decide [ List.count_eq_zero_of_not_mem ];
  · -- If x is in the list, then by the second part of h, x must be equal to result.
    intros x hx
    by_cases hx_in : x ∈ nums;
    · grind +ring;
    · rw [ List.count_eq_zero_of_not_mem hx_in ] at hx ; omega;
  · grind +ring

end Proof