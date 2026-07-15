import Mathlib.Tactic

namespace VerinaSpec


def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length

def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) : Prop :=
  result.length = k ∧
  result.all (· ∈ nums) ∧
  List.Pairwise (· ≠ ·) result ∧
  (result.all (fun x =>
    nums.all (fun y =>
      y ∈ result ∨ nums.count x ≥ nums.count y
    ))) ∧
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x ≥ nums.count y
  ) result.zipIdx

end VerinaSpec

namespace LLMSpec

def freq (nums : List Int) (x : Int) : Nat :=
  nums.count x

def firstIndex (nums : List Int) (x : Int) : Nat :=
  match nums.findIdx? (fun y => y = x) with
  | some i => i
  | none => nums.length

def precedesByFreqThenFirst (nums : List Int) (a : Int) (b : Int) : Prop :=
  let fa := freq nums a
  let fb := freq nums b
  let ia := firstIndex nums a
  let ib := firstIndex nums b
  (fa > fb) ∨ (fa = fb ∧ ia < ib)

def isSortedByFreqThenFirst (nums : List Int) (xs : List Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < xs.length →
    precedesByFreqThenFirst nums xs[i]! xs[j]!

def precondition (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length

def postcondition (nums : List Int) (k : Nat) (result : List Int) : Prop :=
  ∃ (sortedAll : List Int),
    sortedAll.Nodup ∧
    (∀ (x : Int), x ∈ sortedAll ↔ x ∈ nums) ∧
    isSortedByFreqThenFirst nums sortedAll ∧
    result = sortedAll.take k

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) (k : Nat) :
  VerinaSpec.topKFrequent_precond nums k ↔ LLMSpec.precondition nums k := by
  sorry

theorem postcondition_equiv (nums : List Int) (k : Nat) (result: List Int) :
  LLMSpec.precondition nums k →
  (VerinaSpec.topKFrequent_postcond nums k result ↔ LLMSpec.postcondition nums k result) := by
  sorry

end Proof
