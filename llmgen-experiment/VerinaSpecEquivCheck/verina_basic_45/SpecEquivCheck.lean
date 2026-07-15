import Mathlib.Tactic

namespace VerinaSpec


def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none

def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)

def findProduct_postcond (lst : List Int) (result: Int) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True

end VerinaSpec

namespace LLMSpec

-- Helper predicates as Bool so they can be used with List.find?
def isEvenB (n : Int) : Bool := (n % 2) == 0

def isOddB (n : Int) : Bool := (n % 2) == 1

-- The precondition requires existence of at least one even and one odd element.
-- We express this via List.find? returning some value.
def precondition (lst : List Int) : Prop :=
  (lst.find? isEvenB).isSome = true ∧
  (lst.find? isOddB).isSome = true

-- Postcondition: result equals the product of the first even and first odd elements.
-- We pin down “first” using List.find? itself (which is defined as left-to-right search).
def postcondition (lst : List Int) (result : Int) : Prop :=
  ∃ (e : Int) (o : Int),
    lst.find? isEvenB = some e ∧
    lst.find? isOddB = some o ∧
    result = e * o

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) :
  VerinaSpec.findProduct_precond lst ↔ LLMSpec.precondition lst := by
  sorry

theorem postcondition_equiv (lst : List Int) (result: Int) :
  LLMSpec.precondition lst →
  (VerinaSpec.findProduct_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  sorry

end Proof
