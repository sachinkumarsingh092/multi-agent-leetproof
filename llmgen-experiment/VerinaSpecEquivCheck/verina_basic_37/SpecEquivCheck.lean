import Mathlib.Tactic

namespace VerinaSpec


def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) :=
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))

end VerinaSpec

namespace LLMSpec

-- Array is sorted in non-decreasing order.
-- We phrase this using Nat indices and `arr[i]!` with explicit bounds.
def isSortedND (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Precondition: the input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedND arr

-- Postcondition:
-- Either the target is absent and we return -1,
-- or we return `Int.ofNat k` where `k` is the smallest index with `arr[k] = target`.
def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ (i : Nat), i < arr.size → arr[i]! ≠ target)) ∨
  (∃ (k : Nat),
      k < arr.size ∧
      result = Int.ofNat k ∧
      arr[k]! = target ∧
      (∀ (j : Nat), j < k → arr[j]! ≠ target))

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (target : Int) :
  VerinaSpec.findFirstOccurrence_precond arr target ↔ LLMSpec.precondition arr target := by
  sorry

theorem postcondition_equiv (arr : Array Int) (target : Int) (result: Int) :
  LLMSpec.precondition arr target →
  (VerinaSpec.findFirstOccurrence_postcond arr target result ↔ LLMSpec.postcondition arr target result) := by
  sorry

end Proof
