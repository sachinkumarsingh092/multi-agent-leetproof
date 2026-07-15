/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 33dadf33-0e79-480d-8920-b0f86675ff2a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Nat) : VerinaSpec.missingNumber_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Nat) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.missingNumber_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def missingNumber_precond (nums : List Nat) : Prop :=
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums

def missingNumber_postcond (nums : List Nat) (result: Nat) : Prop :=
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums

end VerinaSpec

namespace LLMSpec

-- Helper: predicate stating a Nat is within the expected inclusive range [0, nums.length].
-- Note: lower bound 0 is automatic for Nat.
def inRange0n (nums : List Nat) (x : Nat) : Prop :=
  x ≤ nums.length

-- Preconditions:
-- - no duplicates
-- - all elements are within [0, n]
-- - there exists a missing number in [0, n]
-- - the missing number is unique

def precondition (nums : List Nat) : Prop :=
  nums.Nodup ∧
  (∀ (x : Nat), x ∈ nums → inRange0n nums x) ∧
  (∃ (m : Nat), inRange0n nums m ∧ m ∉ nums) ∧
  (∀ (m1 : Nat) (m2 : Nat),
    inRange0n nums m1 → inRange0n nums m2 → m1 ∉ nums → m2 ∉ nums → m1 = m2)

-- Postconditions:
-- - result is within [0, n]
-- - result is not present in the list
-- - result is the unique missing number in [0, n]

def postcondition (nums : List Nat) (result : Nat) : Prop :=
  inRange0n nums result ∧
  result ∉ nums ∧
  (∀ (x : Nat), inRange0n nums x → x ∉ nums → x = result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Nat) : VerinaSpec.missingNumber_precond nums ↔ LLMSpec.precondition nums := by
  -- To prove the equivalence of the preconditions, we can show that each condition implies the other.
  apply Iff.intro;
  · -- To prove the forward direction, assume the VerinaSpec conditions hold.
    intro h_verina
    obtain ⟨h_distinct, h_range⟩ := h_verina;
    refine' ⟨ h_range, _, _, _ ⟩ <;> simp_all +decide [ LLMSpec.precondition ];
    · assumption;
    · -- Since the list `nums` has length `n` and contains distinct elements, there must be at least one number in the range `[0, n]` that is not in `nums`.
      have h_exists_m : ∃ m ∈ Finset.range (nums.length + 1), m ∉ nums := by
        by_contra h_contra; push_neg at h_contra; (
        exact absurd ( Finset.card_le_card ( show Finset.range ( nums.length + 1 ) ⊆ nums.toFinset from fun x hx => by simpa using h_contra x hx ) ) ( by simp +decide [ Finset.card_range, List.toFinset_card_of_nodup h_range ] ) ;);
      exact ⟨ h_exists_m.choose, Finset.mem_range_succ_iff.mp h_exists_m.choose_spec.1, h_exists_m.choose_spec.2 ⟩;
    · -- Since there's exactly one missing number, any two numbers not in the list must be the same.
      intros m1 m2 hm1 hm2 hm1_not_in hm2_not_in
      have h_unique : ∀ m, m ≤ nums.length → m ∉ nums → m = (Finset.range (nums.length + 1) \ nums.toFinset).sum id := by
        have h_unique : Finset.card (Finset.range (nums.length + 1) \ nums.toFinset) = 1 := by
          rw [ Finset.card_sdiff ] ; norm_num [ Finset.card_range, h_range ];
          rw [ show nums.toFinset ∩ Finset.range ( nums.length + 1 ) = nums.toFinset from Finset.inter_eq_left.mpr <| Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Nat.lt_succ_of_le <| h_distinct x <| List.mem_toFinset.mp hx ] ; simp +decide [ h_range, List.toFinset_card_of_nodup ];
        -- Since the cardinality of the set is 1, the set is a singleton.
        have h_singleton : ∃ x, Finset.range (nums.length + 1) \ nums.toFinset = {x} := by
          exact Finset.card_eq_one.mp h_unique;
        -- Since the set is a singleton, any element in the set must be equal to the element in the singleton.
        obtain ⟨x, hx⟩ := h_singleton;
        simp [hx];
        exact fun m hm hm' => Finset.mem_singleton.mp ( hx ▸ Finset.mem_sdiff.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le hm ), by simpa using hm' ⟩ );
      rw [ h_unique m1 hm1 hm1_not_in, h_unique m2 hm2 hm2_not_in ];
  · -- To prove the forward direction, assume the LLMSpec conditions hold.
    intro h
    obtain ⟨h_nodup, h_range, h_missing, h_unique⟩ := h;
    constructor <;> aesop

theorem postcondition_equiv (nums : List Nat) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.missingNumber_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold VerinaSpec.missingNumber_postcond LLMSpec.postcondition;
  -- By definition of `inRange0n`, we know that `inRange0n nums result` is equivalent to `result ≤ nums.length`.
  simp [LLMSpec.inRange0n];
  grind

end Proof