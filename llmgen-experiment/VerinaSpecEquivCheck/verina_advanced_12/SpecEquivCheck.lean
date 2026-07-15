import Mathlib.Tactic

namespace VerinaSpec


def firstDuplicate_precond (lst : List Int) : Prop :=
  True

def firstDuplicate_postcond (lst : List Int) (result: Option Int) : Prop :=
  match result with
  | none => List.Nodup lst
  | some x =>
    lst.count x > 1 ∧
    (lst.filter (fun y => lst.count y > 1)).head? = some x

end VerinaSpec

namespace LLMSpec

-- Helper: j is a duplicate occurrence if the element at j appears earlier.
-- We include j < lst.length so that all indexing operations are safe.
def DupAt (lst : List Int) (j : Nat) : Prop :=
  j < lst.length ∧ ∃ i : Nat, i < j ∧ lst[i]! = lst[j]!

-- Helper: j is the first index (smallest) that is a duplicate occurrence.
def IsFirstDupIndex (lst : List Int) (j : Nat) : Prop :=
  DupAt lst j ∧ ∀ k : Nat, k < j → ¬ DupAt lst k

-- No input restrictions.
def precondition (lst : List Int) : Prop :=
  True

def postcondition (lst : List Int) (result : Option Int) : Prop :=
  match result with
  | none =>
      -- No position is a duplicate occurrence.
      ∀ j : Nat, j < lst.length → ¬ DupAt lst j
  | some x =>
      -- There is a first duplicate index j, and x is the value at that position.
      ∃ j : Nat, IsFirstDupIndex lst j ∧ lst[j]! = x

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) :
  VerinaSpec.firstDuplicate_precond lst ↔ LLMSpec.precondition lst := by
  sorry

theorem postcondition_equiv (lst : List Int) (result: Option Int) :
  LLMSpec.precondition lst →
  (VerinaSpec.firstDuplicate_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  sorry

end Proof
