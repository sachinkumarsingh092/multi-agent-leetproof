import Mathlib.Tactic

namespace VerinaSpec


def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList

def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))

end VerinaSpec

namespace LLMSpec

-- Helper: sortedness in non-decreasing order (using Nat indices and `arr[i]!`).
def isSortedNondesc (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: element membership expressed via indices.
def contains (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

-- Helper: `k` is a last-occurrence index of `elem`.
def isLastOccurrenceIdx (arr : Array Int) (elem : Int) (k : Nat) : Prop :=
  k < arr.size ∧
  arr[k]! = elem ∧
  ∀ (j : Nat), k < j → j < arr.size → arr[j]! ≠ elem

-- Preconditions: the input array is sorted in non-decreasing order.
def precondition (arr : Array Int) (elem : Int) : Prop :=
  isSortedNondesc arr

-- Postconditions: result is -1 iff `elem` is absent, otherwise result is the (unique) last index.
def postcondition (arr : Array Int) (elem : Int) (result : Int) : Prop :=
  (result = (-1) ∧ (∀ (i : Nat), i < arr.size → arr[i]! ≠ elem)) ∨
  (∃ (k : Nat), result = Int.ofNat k ∧ isLastOccurrenceIdx arr elem k)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (elem : Int) :
  VerinaSpec.lastPosition_precond arr elem ↔ LLMSpec.precondition arr elem := by
  sorry

theorem postcondition_equiv (arr : Array Int) (elem : Int) (result: Int) :
  LLMSpec.precondition arr elem →
  (VerinaSpec.lastPosition_postcond arr elem result ↔ LLMSpec.postcondition arr elem result) := by
  sorry

end Proof
