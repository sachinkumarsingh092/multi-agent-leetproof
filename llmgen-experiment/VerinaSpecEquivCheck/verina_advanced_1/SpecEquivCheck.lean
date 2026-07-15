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

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.FindSingleNumber_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Int) :
  LLMSpec.precondition nums →
  (VerinaSpec.FindSingleNumber_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
