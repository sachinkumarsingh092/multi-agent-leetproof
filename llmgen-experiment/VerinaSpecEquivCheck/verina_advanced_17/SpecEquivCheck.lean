import Mathlib.Tactic

namespace VerinaSpec


def insertionSort_precond (l : List Int) : Prop :=
  True

def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

def insertionSort_postcond (l : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result

end VerinaSpec

namespace LLMSpec

-- We use Mathlib's predicates:
-- * `l.Sorted (· ≤ ·)` for non-decreasing sortedness.
-- * `List.Perm` to express that two lists are permutations (same multiset of elements).

def precondition (l : List Int) : Prop :=
  True

def postcondition (l : List Int) (result : List Int) : Prop :=
  result.Sorted (· ≤ ·) ∧ List.Perm result l

end LLMSpec

section Proof

theorem precondition_equiv (l : List Int) :
  VerinaSpec.insertionSort_precond l ↔ LLMSpec.precondition l := by
  sorry

theorem postcondition_equiv (l : List Int) (result: List Int) :
  LLMSpec.precondition l →
  (VerinaSpec.insertionSort_postcond l result ↔ LLMSpec.postcondition l result) := by
  sorry

end Proof
