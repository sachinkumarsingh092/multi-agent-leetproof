import Mathlib.Tactic

namespace VerinaSpec


def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n

def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))

end VerinaSpec

namespace LLMSpec

-- Helper: non-decreasing sortedness (allows equal neighbors)
def isSortedND (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: absolute difference as a natural number
-- `Int.natAbs` is the nonnegative absolute value of an integer, returned as `Nat`.
def absDiffNat (x : Int) (y : Int) : Nat :=
  Int.natAbs (x - y)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧
  b.size > 0 ∧
  isSortedND a ∧
  isSortedND b

def postcondition (a : Array Int) (b : Array Int) (result : Nat) : Prop :=
  -- Achievability: the minimum value is realized by some pair (i, j)
  (∃ (i : Nat), i < a.size ∧ ∃ (j : Nat), j < b.size ∧ result = absDiffNat a[i]! b[j]!) ∧
  -- Minimality: result is <= every pairwise absolute difference
  (∀ (i : Nat), i < a.size → ∀ (j : Nat), j < b.size → result ≤ absDiffNat a[i]! b[j]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) :
  VerinaSpec.CanyonSearch_precond a b ↔ LLMSpec.precondition a b := by
  sorry

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result: Nat) :
  LLMSpec.precondition a b →
  (VerinaSpec.CanyonSearch_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  sorry

end Proof
