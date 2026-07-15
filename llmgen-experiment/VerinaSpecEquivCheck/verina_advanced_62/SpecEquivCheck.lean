import Mathlib.Tactic

namespace VerinaSpec


def rain_precond (heights : List (Int)) : Prop :=
  heights.all (fun h => h >= 0)

def rain_postcond (heights : List (Int)) (result: Int) : Prop :=
  result >= 0 ∧
  if heights.length < 3 then result = 0 else
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0
      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0
      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)
      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i
      sum_water 0 0

end VerinaSpec

namespace LLMSpec

-- Helper: maximum height seen from the left up to (and including) index i.
-- Defined using take and foldl; for i out of range, it still yields a well-defined value.
def leftMaxUpTo (heights : List Int) (i : Nat) : Int :=
  (heights.take (i + 1)).foldl (init := (0 : Int)) max

-- Helper: maximum height seen from the right starting at index i.
def rightMaxFrom (heights : List Int) (i : Nat) : Int :=
  (heights.drop i).foldl (init := (0 : Int)) max

-- Helper: expected trapped water at index i, defaulting to 0 when i is out of range.
def expectedWaterAt (heights : List Int) (i : Nat) : Int :=
  match heights.get? i with
  | none => 0
  | some h =>
      max 0 (min (leftMaxUpTo heights i) (rightMaxFrom heights i) - h)

-- Preconditions: all heights are non-negative.
def precondition (heights : List Int) : Prop :=
  ∀ (i : Nat), i < heights.length → 0 ≤ (heights.get? i).getD 0

-- Postcondition: there exists a per-index water list whose elements match expectedWaterAt,
-- and result is the sum of these elements.
def postcondition (heights : List Int) (result : Int) : Prop :=
  (0 ≤ result) ∧
  (∃ (water : List Int),
    water.length = heights.length ∧
    water.sum = result ∧
    (∀ (i : Nat), i < heights.length → water.get? i = some (expectedWaterAt heights i)))

end LLMSpec

section Proof

theorem precondition_equiv (heights : List (Int)) :
  VerinaSpec.rain_precond heights ↔ LLMSpec.precondition heights := by
  sorry

theorem postcondition_equiv (heights : List (Int)) (result: Int) :
  LLMSpec.precondition heights →
  (VerinaSpec.rain_postcond heights result ↔ LLMSpec.postcondition heights result) := by
  sorry

end Proof
