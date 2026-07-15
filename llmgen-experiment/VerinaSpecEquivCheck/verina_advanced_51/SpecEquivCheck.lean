import Mathlib.Tactic

namespace VerinaSpec


def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b

def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged

def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) : Prop :=
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)

end VerinaSpec

namespace LLMSpec

-- Helper: non-decreasing sortedness for Int lists.
-- Mathlib provides `List.Sorted`.
def sortedND (l : List Int) : Prop :=
  l.Sorted (fun x y => x ≤ y)

-- Precondition: both input lists are sorted in non-decreasing order.
def precondition (a : List Int) (b : List Int) : Prop :=
  sortedND a ∧ sortedND b

-- Postcondition:
-- 1) result is sorted in non-decreasing order
-- 2) result contains exactly all elements from a and b, counting duplicates
-- 3) result length equals sum of input lengths
-- Note: we avoid `List.toMultiset` (not available in this environment) and instead
-- specify multiplicities using `List.count`.
def postcondition (a : List Int) (b : List Int) (result : List Int) : Prop :=
  sortedND result ∧
  (∀ x : Int, result.count x = a.count x + b.count x) ∧
  result.length = a.length + b.length

end LLMSpec

section Proof

theorem precondition_equiv (a : List Int) (b : List Int) :
  VerinaSpec.mergeSorted_precond a b ↔ LLMSpec.precondition a b := by
  sorry

theorem postcondition_equiv (a : List Int) (b : List Int) (result: List Int) :
  LLMSpec.precondition a b →
  (VerinaSpec.mergeSorted_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  sorry

end Proof
