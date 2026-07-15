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

theorem precondition_equiv (nums : Array Int) (target : Int) :
  VerinaSpec.twoSum_precond nums target ↔ LLMSpec.precondition nums target := by
  sorry

theorem postcondition_equiv (nums : Array Int) (target : Int) (result: Array Nat) :
  LLMSpec.precondition nums target →
  (VerinaSpec.twoSum_postcond nums target result ↔ LLMSpec.postcondition nums target result) := by
  sorry

end Proof
