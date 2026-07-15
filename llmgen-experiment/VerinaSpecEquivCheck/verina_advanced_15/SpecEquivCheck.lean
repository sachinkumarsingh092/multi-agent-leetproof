import Mathlib.Tactic

namespace VerinaSpec


def increasingTriplet_precond (nums : List Int) : Prop :=
  True

def increasingTriplet_postcond (nums : List Int) (result: Bool) : Prop :=
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))

end VerinaSpec

namespace LLMSpec

-- There exists a strictly increasing subsequence of length 3, witnessed by indices i<j<k.
-- We use `nums[i]!` with an explicit bound `k < nums.length` to ensure all accesses are in range.
def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ (i : Nat) (j : Nat) (k : Nat),
    i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!

def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Bool) : Prop :=
  result = true ↔ hasIncreasingTriplet nums

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.increasingTriplet_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Bool) :
  LLMSpec.precondition nums →
  (VerinaSpec.increasingTriplet_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
