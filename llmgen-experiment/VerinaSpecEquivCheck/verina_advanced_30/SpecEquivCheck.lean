import Mathlib.Tactic

namespace VerinaSpec


def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  True

def longestIncreasingStreak_postcond (nums : List Int) (result: Nat) : Prop :=
  (nums = [] → result = 0) ∧
  (result > 0 →
    (List.range (nums.length - result + 1) |>.any (fun start =>
      start + result ≤ nums.length ∧
      (List.range (result - 1) |>.all (fun i =>
        nums[start + i]! < nums[start + i + 1]!)) ∧
      (start = 0 ∨ nums[start - 1]! ≥ nums[start]!) ∧
      (start + result = nums.length ∨ nums[start + result - 1]! ≥ nums[start + result]!)))) ∧
  (List.range (nums.length - result) |>.all (fun start =>
    List.range result |>.any (fun i =>
      start + i + 1 ≥ nums.length ∨ nums[start + i]! ≥ nums[start + i + 1]!)))

end VerinaSpec

namespace LLMSpec

-- A segment of `nums` starting at index `start` with length `len` is strictly increasing
-- if every adjacent pair within the segment increases.
-- This predicate is only intended to be used when `start + len ≤ nums.length`.
def StrictIncSegment (nums : List Int) (start : Nat) (len : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < len → nums.get! (start + i) < nums.get! (start + i + 1)

-- Precondition: no restrictions.
def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Nat) : Prop :=
  -- Empty list case
  (nums = [] → result = 0) ∧
  -- Non-empty list case bounds
  (nums ≠ [] → 1 ≤ result ∧ result ≤ nums.length) ∧
  -- Achievability: there exists a strictly increasing segment of length `result`
  (∃ (start : Nat), start + result ≤ nums.length ∧ StrictIncSegment nums start result) ∧
  -- Maximality: any strictly increasing segment length is bounded by `result`
  (∀ (start : Nat) (len : Nat),
      start + len ≤ nums.length →
      StrictIncSegment nums start len →
      len ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.longestIncreasingStreak_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Nat) :
  LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingStreak_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
