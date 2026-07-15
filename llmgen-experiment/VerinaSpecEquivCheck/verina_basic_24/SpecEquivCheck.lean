import Mathlib.Tactic

namespace VerinaSpec


def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0

def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

def firstEvenOddDifference_postcond (a : Array Int) (result: Int) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))

end VerinaSpec

namespace LLMSpec

-- Helper predicates for parity using Int modulo.
-- With divisor 2 > 0, Int.mod returns 0 or 1.
def isEven (n : Int) : Prop := n % 2 = 0

def isOdd (n : Int) : Prop := n % 2 = 1

-- `i` is the index of the first even element in `a`.
def isFirstEvenIdx (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧
  isEven (a[i]!) ∧
  ∀ (j : Nat), j < i → ¬ isEven (a[j]!)

-- `i` is the index of the first odd element in `a`.
def isFirstOddIdx (a : Array Int) (i : Nat) : Prop :=
  i < a.size ∧
  isOdd (a[i]!) ∧
  ∀ (j : Nat), j < i → ¬ isOdd (a[j]!)

-- Precondition: array is non-empty and contains at least one even and at least one odd.
def precondition (a : Array Int) : Prop :=
  a.size > 0 ∧
  (∃ (i : Nat), i < a.size ∧ isEven (a[i]!)) ∧
  (∃ (i : Nat), i < a.size ∧ isOdd (a[i]!))

-- Postcondition: result equals (first even) - (first odd).
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (iEven : Nat) (iOdd : Nat),
    isFirstEvenIdx a iEven ∧
    isFirstOddIdx a iOdd ∧
    result = a[iEven]! - a[iOdd]!

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) :
  VerinaSpec.firstEvenOddDifference_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result: Int) :
  LLMSpec.precondition a →
  (VerinaSpec.firstEvenOddDifference_postcond a result ↔ LLMSpec.postcondition a result) := by
  sorry

end Proof
