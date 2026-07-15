import Mathlib.Tactic

namespace VerinaSpec


def secondSmallest_precond (s : Array Int) : Prop :=
  s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!  -- at least two distinct values

def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i

def secondSmallest_postcond (s : Array Int) (result: Int) :=
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)

end VerinaSpec

namespace LLMSpec

-- Membership predicate for arrays, phrased using Nat indices (preferred for specs).
def InArray (s : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < s.size ∧ s[i]! = x

-- At least two distinct elements occur in the array.
def HasTwoDistinct (s : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!

-- Preconditions: size ≥ 2 and at least two distinct values.
def precondition (s : Array Int) : Prop :=
  s.size ≥ 2 ∧ HasTwoDistinct s

-- Postcondition: result is the least element strictly greater than the minimum element of s.
def postcondition (s : Array Int) (result : Int) : Prop :=
  ∃ (m : Int),
    s.min? = some m ∧
    InArray s m ∧
    (∀ (x : Int), InArray s x → m ≤ x) ∧
    InArray s result ∧
    m < result ∧
    (∀ (x : Int), InArray s x → m < x → result ≤ x)

end LLMSpec

section Proof

theorem precondition_equiv (s : Array Int) :
  VerinaSpec.secondSmallest_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : Array Int) (result: Int) :
  LLMSpec.precondition s →
  (VerinaSpec.secondSmallest_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
