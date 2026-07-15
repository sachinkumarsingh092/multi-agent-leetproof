import Mathlib.Tactic

namespace VerinaSpec


def trapRainWater_precond (height : List Nat) : Prop :=
  True

def trapRainWater_postcond (height : List Nat) (result: Nat) : Prop :=
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)
  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result

end VerinaSpec

namespace LLMSpec

-- A characterization that `m` is the maximum height on the prefix {0..i} (inclusive),
-- assuming `i` is a valid index (< height.length).
-- This is expressed as:
--   (1) every prefix element is ≤ m (upper bound)
--   (2) some prefix element equals m (attainment)
def isPrefixMax (height : List Nat) (i : Nat) (m : Nat) : Prop :=
  i < height.length ∧
  (∀ (j : Nat), j ≤ i → j < height.length → height[j]! ≤ m) ∧
  (∃ (j : Nat), j ≤ i ∧ j < height.length ∧ height[j]! = m)

-- A characterization that `m` is the maximum height on the suffix {i..n-1} (inclusive),
-- assuming `i` is a valid index (< height.length).
def isSuffixMax (height : List Nat) (i : Nat) (m : Nat) : Prop :=
  i < height.length ∧
  (∀ (j : Nat), i ≤ j → j < height.length → height[j]! ≤ m) ∧
  (∃ (j : Nat), i ≤ j ∧ j < height.length ∧ height[j]! = m)

-- Water trapped at index i; defined as 0 for out-of-bounds indices to keep it total.
def waterAt (height : List Nat) (i : Nat) : Nat :=
  if h : i < height.length then
    let hi : Nat := height[i]!
    -- Choose left/right maxima concretely for the computation; the postcondition will relate them
    -- to the abstract maximum characterization.
    let lmax : Nat := (height.take (i + 1)).foldl Nat.max 0
    let rmax : Nat := (height.drop i).foldl Nat.max 0
    (Nat.min lmax rmax) - hi
  else
    0

-- Precondition: no restrictions beyond the stated domain (List Nat is already non-negative).
-- We mention `height` to avoid unused-variable warnings.
def precondition (height : List Nat) : Prop :=
  height.length = height.length

-- Postcondition:
-- There exist functions L and R giving, for each valid index i,
-- the prefix and suffix maxima respectively.
-- The result is the sum over indices of min(L i, R i) - height[i] (truncated subtraction).
def postcondition (height : List Nat) (result : Nat) : Prop :=
  let n : Nat := height.length
  (∃ (L : Nat → Nat),
    (∀ (i : Nat), i < n → isPrefixMax height i (L i)) ∧
    (∃ (R : Nat → Nat),
      (∀ (i : Nat), i < n → isSuffixMax height i (R i)) ∧
      result = (List.range n).foldl
        (fun (acc : Nat) (i : Nat) => acc + (Nat.min (L i) (R i) - height[i]!))
        0))

end LLMSpec

section Proof

theorem precondition_equiv (height : List Nat) :
  VerinaSpec.trapRainWater_precond height ↔ LLMSpec.precondition height := by
  sorry

theorem postcondition_equiv (height : List Nat) (result: Nat) :
  LLMSpec.precondition height →
  (VerinaSpec.trapRainWater_postcond height result ↔ LLMSpec.postcondition height result) := by
  sorry

end Proof
