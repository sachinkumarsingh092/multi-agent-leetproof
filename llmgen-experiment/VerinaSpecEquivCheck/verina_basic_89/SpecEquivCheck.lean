import Mathlib.Tactic

namespace VerinaSpec


def SetToSeq_precond (s : List Int) : Prop :=
  True

def SetToSeq_postcond (s : List Int) (result: List Int) :=
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  result.all (fun a => result.count a = 1) ∧
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result

end VerinaSpec

namespace LLMSpec

-- x has its first occurrence in s exactly at position p.
-- This characterizes first occurrence without using any library index-finding API.
def FirstOccurrenceAt (x : Int) (s : List Int) (p : Nat) : Prop :=
  p < s.length ∧
  s[p]! = x ∧
  ∀ q : Nat, q < p → s[q]! ≠ x

def precondition (s : List Int) : Prop :=
  True

def postcondition (s : List Int) (result : List Int) : Prop :=
  -- No duplicates in the output.
  result.Nodup ∧
  -- Output contains exactly the elements that appear in the input.
  (∀ x : Int, x ∈ result ↔ x ∈ s) ∧
  -- Every output element is taken at its first occurrence position in s.
  (∀ i : Nat, i < result.length → ∃ p : Nat, FirstOccurrenceAt (result[i]!) s p) ∧
  -- The first-occurrence positions of elements of result are strictly increasing in result order.
  (∀ i j : Nat, i < j → j < result.length →
    ∃ pi pj : Nat,
      FirstOccurrenceAt (result[i]!) s pi ∧
      FirstOccurrenceAt (result[j]!) s pj ∧
      pi < pj)

end LLMSpec

section Proof

theorem precondition_equiv (s : List Int) :
  VerinaSpec.SetToSeq_precond s ↔ LLMSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : List Int) (result: List Int) :
  LLMSpec.precondition s →
  (VerinaSpec.SetToSeq_postcond s result ↔ LLMSpec.postcondition s result) := by
  sorry

end Proof
