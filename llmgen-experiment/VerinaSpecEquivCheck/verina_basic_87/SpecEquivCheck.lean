import Mathlib.Tactic

namespace VerinaSpec


def SelectionSort_precond (a : Array Int) : Prop :=
  True

def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

def SelectionSort_postcond (a : Array Int) (result: Array Int) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList

end VerinaSpec

namespace LLMSpec

-- Helper: non-decreasing sortedness for arrays using Nat indices.
-- Strong form: for all i < j within bounds, arr[i] ≤ arr[j].
def ArrayNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: count how many times a value occurs in an array.
-- This is a purely observational property used to express multiset equality.
def elemCount (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if decide (x = v) then acc + 1 else acc) 0

-- Helper: two arrays contain exactly the same multiset of elements (same size and same counts).
def SameMultiset (x : Array Int) (y : Array Int) : Prop :=
  x.size = y.size ∧
  ∀ (v : Int), elemCount x v = elemCount y v

-- No preconditions: any array is a valid input to sorting.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ArrayNondecreasing result ∧
  SameMultiset result a

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) :
  VerinaSpec.SelectionSort_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result: Array Int) :
  LLMSpec.precondition a →
  (VerinaSpec.SelectionSort_postcond a result ↔ LLMSpec.postcondition a result) := by
  sorry

end Proof
