/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e897aefb-6910-4d84-97e4-7e6c7ccfab08
To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
The following was proved by Aristotle:
- theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) : LLMSpec.precondition nums k →
  (VerinaSpec.longestGoodSubarray_postcond nums k result ↔ LLMSpec.postcondition nums k result)
-/
import Mathlib.Tactic
import Std.Data.HashMap
namespace VerinaSpec
open Std
def longestGoodSubarray_precond (nums : List Nat) (k : Nat) : Prop :=
  k > 0
-- k must be positive for non-trivial subarrays
def longestGoodSubarray_postcond (nums : List Nat) (k : Nat) (result: Nat) : Prop :=
  let subArrays :=
    List.range (nums.length + 1) |>.flatMap (fun start =>
      List.range (nums.length - start + 1) |>.map (fun len =>
        nums.drop start |>.take len))
  let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x))
  let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k))
  (nums = [] ∧ result = 0) ∨
  (nums ≠ [] ∧
    validSubArrays.any (fun arr => arr.length = result) ∧
    validSubArrays.all (fun arr => arr.length ≤ result))
end VerinaSpec
namespace LLMSpec
-- A subarray of nums is represented as (nums.drop start).take len.
-- We treat it as valid when len > 0 and start + len ≤ nums.length.
def IsValidSlice (nums : List Nat) (start : Nat) (len : Nat) : Prop :=
  len > 0 ∧ start + len ≤ nums.length
-- A slice is good when every element in it occurs at most k times within that slice.
-- We quantify only over values that appear in the slice (guarded by membership).
def GoodSlice (slice : List Nat) (k : Nat) : Prop :=
  ∀ (x : Nat), x ∈ slice → slice.count x ≤ k
-- Preconditions
-- k must be positive.
def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0
-- Postconditions
-- 1. result is within bounds.
-- 2. If nums is empty, result is 0.
-- 3. If nums is non-empty, there exists a good slice achieving length = result.
-- 4. result is maximal: every good slice length is ≤ result.
def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=
  result ≤ nums.length ∧
  ((nums = []) → result = 0) ∧
  ((nums ≠ []) →
    (∃ (start : Nat) (len : Nat),
      IsValidSlice nums start len ∧
      len = result ∧
      GoodSlice ((nums.drop start).take len) k)) ∧
  (∀ (start : Nat) (len : Nat),
    IsValidSlice nums start len →
    GoodSlice ((nums.drop start).take len) k →
    len ≤ result)
end LLMSpec
section Proof

theorem precondition_equiv (nums : List Nat) (k : Nat) : VerinaSpec.longestGoodSubarray_precond nums k ↔ LLMSpec.precondition nums k := by
  -- The preconditions are equivalent because they both require k to be positive.
  simp [VerinaSpec.longestGoodSubarray_precond, LLMSpec.precondition]

set_option maxHeartbeats 1000000

theorem postcondition_equiv (nums : List Nat) (k : Nat) (result : Nat) : LLMSpec.precondition nums k →
  (VerinaSpec.longestGoodSubarray_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  -- By definition of `postcondition`, we need to show that if `k > 0`, then the VerinaSpec and LLMSpec postconditions are equivalent.
  intro hk
  apply Iff.intro;
  · intro h;
    -- If the VerinaSpec postcondition holds, then the LLMSpec postcondition must also hold because the result is within the bounds and there exists a good slice of length result.
    apply And.intro;
    · cases h <;> aesop;
    · cases h <;> simp_all +decide [ VerinaSpec.longestGoodSubarray_postcond ];
      · unfold LLMSpec.IsValidSlice; aesop;
      · apply And.intro;
        · obtain ⟨ x, hx, y, hy, hxy, rfl ⟩ := ‹¬nums = [] ∧ ( ∃ x < nums.length + 1, ∃ x_1 < nums.length - x + 1, ( ∀ x_2 ∈ List.take x_1 ( List.drop x ( List.map ( fun x_3 => List.count x_3 ( List.take x_1 ( List.drop x nums ) ) ) nums ) ), x_2 ≤ k ) ∧ Min.min x_1 ( nums.length - x ) = result ) ∧ ∀ x < nums.length + 1, ∀ x_1 < nums.length - x + 1, ( ∃ x_2 ∈ List.take x_1 ( List.drop x ( List.map ( fun x_3 => List.count x_3 ( List.take x_1 ( List.drop x nums ) ) ) nums ) ), k < x_2 ) ∨ x_1 ≤ result ∨ nums.length ≤ result + x›.2.1;
          refine' ⟨ x, _, _ ⟩ <;> simp_all +decide [ LLMSpec.IsValidSlice, LLMSpec.GoodSlice ];
          · cases y <;> cases nums <;> simp_all +arith +decide [ List.take_append ];
            · rename_i h; specialize h; rcases h with ⟨ ⟨ x, hx, y, hy, hxy, h ⟩, h' ⟩ ; specialize h' 0 ; simp_all +decide ;
              specialize h' 1 ; simp_all +decide [ List.count ];
              exact absurd hk ( by unfold LLMSpec.precondition; aesop );
            · omega;
          · intro z hz; specialize hxy ( List.count z ( List.take y ( List.drop x nums ) ) ) ; simp_all +decide [ List.mem_iff_get ] ;
            convert hxy ⟨ hz.choose.val, _ ⟩ _ using 1 <;> simp_all +decide [ List.count ];
            any_goals rw [ hz.choose_spec ];
            · rw [ min_eq_left ] ; omega;
            · exact ⟨ lt_of_lt_of_le ( Fin.is_lt _ ) ( by simp ), lt_of_lt_of_le ( Fin.is_lt _ ) ( by simp ) ⟩;
        · intro start len hstart hlen; specialize ‹¬nums = [] ∧ ( ∃ x < nums.length + 1, ∃ x_1 < nums.length - x + 1, ( ∀ x_2 ∈ List.take x_1 ( List.drop x ( List.map ( fun x_3 => List.count x_3 ( List.take x_1 ( List.drop x nums ) ) ) nums ) ), x_2 ≤ k ) ∧ Min.min x_1 ( nums.length - x ) = result ) ∧ ∀ x < nums.length + 1, ∀ x_1 < nums.length - x + 1, ( ∃ x_2 ∈ List.take x_1 ( List.drop x ( List.map ( fun x_3 => List.count x_3 ( List.take x_1 ( List.drop x nums ) ) ) nums ) ), k < x_2 ) ∨ x_1 ≤ result ∨ nums.length ≤ result + x›; simp_all +decide [ LLMSpec.IsValidSlice, LLMSpec.GoodSlice ] ;
          rename_i h; specialize h; have := h.2.2 start ( by linarith ) len ( by omega ) ; simp_all +decide [ List.take_append, List.drop_append ] ;
          contrapose! this; simp_all +decide [ List.take_append, List.drop_append ] ;
          refine' ⟨ _, by linarith ⟩;
          intro x hx; rw [ List.mem_iff_get ] at hx; obtain ⟨ i, hi ⟩ := hx; simp_all +decide [ List.get ] ;
          exact hi ▸ hlen _ ( by
            rw [ List.mem_iff_get ] ; use ⟨ i, by
              exact lt_of_lt_of_le i.2 ( by simp ) ⟩ ; simp +decide [ List.get ] ; );
  · rintro ⟨ h₁, h₂, h₃, h₄ ⟩;
    by_cases h : nums = [] <;> simp_all +decide [ VerinaSpec.longestGoodSubarray_postcond ];
    constructor;
    · obtain ⟨ start, hstart₁, hstart₂ ⟩ := h₃;
      refine' ⟨ start, _, result, _, _, _ ⟩ <;> simp_all +decide [ LLMSpec.IsValidSlice ];
      · grind;
      · omega;
      · intro x hx; have := List.mem_map.mp ( show x ∈ List.map ( fun x => List.count x ( List.take result ( List.drop start nums ) ) ) ( List.take result ( List.drop start nums ) ) from by aesop ) ; aesop;
      · exact le_tsub_of_add_le_left hstart₁.2;
    · contrapose! h₄;
      obtain ⟨ x, hx₁, y, hy₁, hy₂, hy₃, hy₄ ⟩ := h₄;
      refine' ⟨ x, y, ⟨ by linarith, by omega ⟩, _, hy₃ ⟩;
      intro z hz; specialize hy₂ ( List.count z ( List.take y ( List.drop x nums ) ) ) ; simp_all +decide [ List.mem_iff_get ] ;
      grind
end Proof
