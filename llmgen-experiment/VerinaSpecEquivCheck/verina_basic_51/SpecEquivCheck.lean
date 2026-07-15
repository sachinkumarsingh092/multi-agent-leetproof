import Mathlib.Tactic

namespace VerinaSpec


def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  List.Pairwise (· ≤ ·) a.toList

def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo

def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) :=
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))

end VerinaSpec

namespace LLMSpec

-- Array is sorted in non-decreasing order.
def isSortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- Lower-bound / insertion index property.
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNondecreasing a

def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  result ≤ a.size ∧
  (∀ (i : Nat), i < result → a[i]! < key) ∧
  (∀ (i : Nat), result ≤ i → i < a.size → key ≤ a[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (key : Int) :
  VerinaSpec.BinarySearch_precond a key ↔ LLMSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array Int) (key : Int) (result: Nat) :
  LLMSpec.precondition a key →
  (VerinaSpec.BinarySearch_postcond a key result ↔ LLMSpec.postcondition a key result) := by
  sorry

end Proof
