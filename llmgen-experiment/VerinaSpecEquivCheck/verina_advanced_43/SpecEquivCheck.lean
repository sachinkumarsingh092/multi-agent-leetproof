import Mathlib.Tactic
import Mathlib

namespace VerinaSpec


def maxStrength_precond (nums : List Int) : Prop :=
  nums ≠ []

def maxStrength_postcond (nums : List Int) (result: Int) : Prop :=
  let sublists := nums.sublists.filter (· ≠ [])
  let products := sublists.map (List.foldl (· * ·) 1)
  products.contains result ∧ products.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- Helper: product of a list of integers.
-- We use `foldl` to avoid relying on any additional list algebra imports.
-- Convention: the product of an empty list is 1, but empty selections are forbidden by `IsValidSelection`.
def listProd (xs : List Int) : Int :=
  xs.foldl (fun (acc : Int) (x : Int) => acc * x) 1

-- A valid selection is a non-empty sublist (order-preserving) of the original list.
def IsValidSelection (nums : List Int) (s : List Int) : Prop :=
  List.Sublist s nums ∧ s ≠ []

def precondition (nums : List Int) : Prop :=
  nums ≠ []

def postcondition (nums : List Int) (result : Int) : Prop :=
  -- Achievability: the result equals the product of some non-empty valid selection.
  (∃ s : List Int,
      IsValidSelection nums s ∧
      listProd s = result) ∧
  -- Maximality: every non-empty valid selection has product at most `result`.
  (∀ s : List Int,
      IsValidSelection nums s →
      listProd s ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.maxStrength_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Int) :
  LLMSpec.precondition nums →
  (VerinaSpec.maxStrength_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
