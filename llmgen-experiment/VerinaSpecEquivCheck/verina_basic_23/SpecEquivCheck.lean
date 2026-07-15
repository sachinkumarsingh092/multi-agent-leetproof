import Mathlib.Tactic

namespace VerinaSpec


def differenceMinMax_precond (a : Array Int) : Prop :=
  a.size > 0

def differenceMinMax_postcond (a : Array Int) (result: Int) :=
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))

end VerinaSpec

namespace LLMSpec

-- Helper predicates describing when a value occurs in an array.
def occursIn (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

-- Upper/lower bound properties over all indices of the array.
def isUpperBound (a : Array Int) (v : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≤ v

def isLowerBound (a : Array Int) (v : Int) : Prop :=
  ∀ (i : Nat), i < a.size → v ≤ a[i]!

-- Characterization of maximum/minimum values (as elements + bound properties).
def isMaxValue (a : Array Int) (v : Int) : Prop :=
  occursIn a v ∧ isUpperBound a v

def isMinValue (a : Array Int) (v : Int) : Prop :=
  occursIn a v ∧ isLowerBound a v

-- Preconditions
-- The array must be non-empty.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result equals (max - min) for some max and min values of the array.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (maxV : Int) (minV : Int),
    isMaxValue a maxV ∧
    isMinValue a minV ∧
    result = maxV - minV

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) :
  VerinaSpec.differenceMinMax_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result: Int) :
  LLMSpec.precondition a →
  (VerinaSpec.differenceMinMax_postcond a result ↔ LLMSpec.postcondition a result) := by
  sorry

end Proof
