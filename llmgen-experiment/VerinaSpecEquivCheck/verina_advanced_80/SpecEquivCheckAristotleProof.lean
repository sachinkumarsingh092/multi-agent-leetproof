/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f2f2b752-b6ab-4195-9843-0f6e8813558e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : Array Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target

- theorem postcondition_equiv (nums : Array Int) (target : Int) (result : Array Nat) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size ≥ 2 ∧
  (List.range nums.size).any (fun i =>
    (List.range i).any (fun j => nums[i]! + nums[j]! = target)) ∧
  ((List.range nums.size).flatMap (fun i =>
    (List.range i).filter (fun j => nums[i]! + nums[j]! = target))).length = 1

def twoSum_postcond (nums : Array Int) (target : Int) (result: Array Nat) : Prop :=
  result.size = 2 ∧
  result[0]! < nums.size ∧ result[1]! < nums.size ∧
  result[0]! < result[1]! ∧
  nums[result[0]!]! + nums[result[1]!]! = target

end VerinaSpec

namespace LLMSpec

-- A pair (i,j) is a valid two-sum witness when it is in bounds, ordered, and sums to target.
def TwoSumPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- There exists exactly one ordered pair (i<j) in bounds whose values sum to target.
def HasUniqueTwoSum (nums : Array Int) (target : Int) : Prop :=
  ∃ i j : Nat,
    TwoSumPair nums target i j ∧
    (∀ i' j' : Nat, TwoSumPair nums target i' j' → i' = i ∧ j' = j)

-- Preconditions: the input must have exactly one solution.
def precondition (nums : Array Int) (target : Int) : Prop :=
  HasUniqueTwoSum nums target

-- Postconditions: result encodes that unique solution as two sorted indices.
def postcondition (nums : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  result[0]! < result[1]! ∧
  result[1]! < nums.size ∧
  nums[result[0]!]! + nums[result[1]!]! = target ∧
  (∀ i j : Nat, TwoSumPair nums target i j → i = result[0]! ∧ j = result[1]!)

end LLMSpec

section Proof

theorem precondition_equiv (nums : Array Int) (target : Int) : VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  constructor <;> intro h;
  · -- Since the length of the list of pairs is 1, there is exactly one pair (i, j) in the list.
    obtain ⟨i, j, hij⟩ : ∃ i j, i < nums.size ∧ j < nums.size ∧ i < j ∧ nums[i]! + nums[j]! = target ∧ ∀ i' j', i' < nums.size → j' < nums.size → i' < j' → nums[i']! + nums[j']! = target → i' = i ∧ j' = j := by
      obtain ⟨i, j, hij⟩ : ∃ i j, i < nums.size ∧ j < nums.size ∧ i < j ∧ nums[i]! + nums[j]! = target ∧ ∀ i' j', i' < nums.size → j' < nums.size → i' < j' → nums[i']! + nums[j']! = target → (i', j') = (i, j) := by
        obtain ⟨p, hp⟩ : ∃ p : List (Nat × Nat), p.length = 1 ∧ (∀ (q : Nat × Nat), q ∈ p → q.1 < nums.size ∧ q.2 < nums.size ∧ q.1 < q.2 ∧ nums[q.1]! + nums[q.2]! = target) ∧ (∀ (q : Nat × Nat), q.1 < nums.size → q.2 < nums.size → q.1 < q.2 → nums[q.1]! + nums[q.2]! = target → q ∈ p) := by
          use (List.range nums.size).flatMap (fun i => (List.range i).filter (fun j => nums[i]! + nums[j]! = target) |>.map (fun j => (j, i)));
          -- The length of the list is 1 by hypothesis.
          have h_length : (List.flatMap (fun i => List.map (fun j => (j, i)) (List.filter (fun j => nums[i]! + nums[j]! = target) (List.range i))) (List.range nums.size)).length = 1 := by
            have := h.2.2; aesop;
          simp +zetaDelta at *;
          exact ⟨ h_length, by intros; subst_vars; exact ⟨ by linarith, by linarith, by linarith, by linarith ⟩, by intros; exact ⟨ by linarith, by linarith, by linarith ⟩ ⟩;
        rcases List.length_eq_one_iff.mp hp.1 with ⟨ q, rfl ⟩ ; use q.1, q.2 ; aesop;
      exact ⟨ i, j, hij.1, hij.2.1, hij.2.2.1, hij.2.2.2.1, fun i' j' hi' hj' hij' h => by simpa using hij.2.2.2.2 i' j' hi' hj' hij' h ⟩;
    use i, j;
    -- By definition of TwoSumPair, we need to show that i < j, j < nums.size, and nums[i]! + nums[j]! = target.
    simp [LLMSpec.TwoSumPair, hij];
    grind;
  · obtain ⟨ i, j, hij, h ⟩ := h;
    constructor <;> norm_num [ LLMSpec.TwoSumPair ] at *;
    · linarith;
    · refine' ⟨ ⟨ j, hij.2.1, i, hij.1, by linarith ⟩, _ ⟩;
      -- Since there is exactly one pair (i, j) such that i < j and nums[i]! + nums[j]! = target, the sum of the lengths of the filtered lists is 1.
      have h_sum : ∑ a ∈ Finset.range nums.size, (Finset.filter (fun j => nums[a]! + nums[j]! = target) (Finset.range a)).card = 1 := by
        rw [ Finset.sum_eq_single j ] <;> norm_num [ hij ];
        · rw [ Finset.card_eq_one ];
          use i;
          grind;
        · grind +ring;
      convert h_sum using 1

theorem postcondition_equiv (nums : Array Int) (target : Int) (result : Array Nat) : LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  rintro ⟨ i, j, h₁, h₂ ⟩;
  constructor <;> rintro ⟨ h₃, h₄, h₅, h₆ ⟩;
  · refine' ⟨ h₃, h₆.1, h₅, h₆.2, _ ⟩;
    intro i' j' h₇; have := h₂ i' j' h₇; have := h₂ _ _ ⟨ h₆.1, h₅, h₆.2 ⟩ ; aesop;
  · constructor <;> try linarith! [ h₆.2 i j h₁ ] ;
    exact ⟨ lt_trans h₄ h₅, h₅, h₄, h₆.1 ⟩

end Proof