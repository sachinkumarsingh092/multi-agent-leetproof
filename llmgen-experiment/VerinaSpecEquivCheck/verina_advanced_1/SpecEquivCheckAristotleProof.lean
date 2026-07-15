/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 93b38886-d8ff-463a-bc99-fbea8ad510b2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.FindSingleNumber_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.FindSingleNumber_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums

def FindSingleNumber_precond (nums : List Int) : Prop :=
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1

def FindSingleNumber_postcond (nums : List Int) (result: Int) : Prop :=
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))

end VerinaSpec

namespace LLMSpec

-- There is exactly one value with count = 1, and every other value has count 0 or 2.
-- This property already implies the list is non-empty.
def hasSingleWithPairs (nums : List Int) : Prop :=
  ∃ x : Int,
    nums.count x = 1 ∧
    (∀ y : Int, nums.count y = 1 → y = x) ∧
    (∀ y : Int, y ≠ x → (nums.count y = 0 ∨ nums.count y = 2))

-- Preconditions: the input list satisfies the intended “pairs except one” shape.
def precondition (nums : List Int) : Prop :=
  hasSingleWithPairs nums

-- Postcondition: the returned value is exactly the unique element with count = 1.
def postcondition (nums : List Int) (result : Int) : Prop :=
  nums.count result = 1 ∧ (∀ y : Int, nums.count y = 1 → y = result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.FindSingleNumber_precond nums ↔ LLMSpec.precondition nums := by
  constructor;
  · rintro ⟨ h₁, h₂ ⟩;
    obtain ⟨x, hx⟩ : ∃ x : ℤ, nums.count x = 1 ∧ ∀ y : ℤ, y ∈ nums → (nums.count y = 1 → y = x) := by
      -- Since there's exactly one element with count 1, we can pick any such element and show that it must be unique.
      obtain ⟨x, hx⟩ : ∃ x : ℤ, x ∈ nums ∧ nums.count x = 1 := by
        contrapose! h₂;
        rw [ List.count_eq_zero_of_not_mem ] <;> aesop;
      refine' ⟨ x, hx.2, fun y hy hy' => _ ⟩;
      contrapose! h₂;
      rw [ List.count ];
      rw [ List.countP_map ];
      rw [ List.countP_eq_length_filter ];
      refine' ne_of_gt ( lt_of_lt_of_le _ ( List.toFinset_card_le _ ) );
      refine' Finset.one_lt_card.mpr ⟨ x, _, y, _, _ ⟩ <;> aesop;
    refine' ⟨ x, hx.1, fun y hy => _, fun y hy => _ ⟩;
    · by_cases hy' : y ∈ nums <;> simp_all +decide [ List.count_eq_zero_of_not_mem ];
      exact hx.2 y hy' hy;
    · by_cases hy' : y ∈ nums <;> simp_all +decide [ List.count_eq_zero ];
      cases h₁ y hy' <;> simp_all +decide;
      exact hy ( hx.2 y hy' ‹_› );
  · intro h;
    -- Let's obtain the unique element `x` with count 1 from the hypothesis `h`.
    obtain ⟨x, hx_count, hx_unique, hx_pairs⟩ := h;
    constructor;
    · simp_all +decide [ List.count_eq_zero ];
      grind +ring;
    · -- Since there's exactly one x with count 1, the count of 1 in the list of counts is 1.
      have h_count_one : List.count 1 (List.map (fun x => List.count x nums) nums) = List.count x nums := by
        rw [ List.count ];
        rw [ List.countP_map ];
        exact List.countP_congr fun y hy => by specialize hx_unique y; specialize hx_pairs y; aesop;
      linarith

theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.FindSingleNumber_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  -- If the precondition holds, then the postcondition and the postcondition are equivalent because they both describe the same situation where there's exactly one element with count 1.
  intro h_precond
  simp [VerinaSpec.FindSingleNumber_postcond, LLMSpec.postcondition];
  -- By definition of `filterlist`, the length of the filtered list of `x` in `nums` is equal to the count of `x` in `nums`.
  have h_filterlist_count : ∀ x, (VerinaSpec.filterlist x nums).length = nums.count x := by
    intro x
    have h_filterlist_count_aux : ∀ (lst : List ℤ), (VerinaSpec.filterlist.aux x lst).length = lst.count x := by
      intro lst
      induction' lst with y ys ih;
      · rfl;
      · by_cases hy : y = x <;> simp_all +decide [ VerinaSpec.filterlist.aux ]
    exact h_filterlist_count_aux nums;
  obtain ⟨ x, hx ⟩ := h_precond;
  by_cases h : result = x <;> simp_all +decide [ List.count_eq_zero ];
  · grind;
  · grind

end Proof