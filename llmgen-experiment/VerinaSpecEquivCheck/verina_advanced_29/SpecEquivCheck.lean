import Mathlib.Tactic
import Std.Data.HashMap

namespace VerinaSpec

open Std

def longestGoodSubarray_precond (nums : List Nat) (k : Nat) : Prop :=
  k > 0  -- k must be positive for non-trivial subarrays

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

theorem postcondition_equiv (nums : List Nat) (k : Nat) (result: Nat) :
  LLMSpec.precondition nums k →
  (VerinaSpec.longestGoodSubarray_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  sorry

end Proof
