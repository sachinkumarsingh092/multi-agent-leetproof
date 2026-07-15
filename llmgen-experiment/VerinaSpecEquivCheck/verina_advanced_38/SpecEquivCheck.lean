import Mathlib.Tactic

namespace VerinaSpec


def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  intervals.length > 0

def maxCoverageAfterRemovingOne_postcond (intervals : List (Prod Nat Nat)) (result: Nat) : Prop :=
  ∃ i < intervals.length,
    let remaining := List.eraseIdx intervals i
    let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
    let merged := sorted.foldl (fun acc curr =>
      match acc with
      | [] => [curr]
      | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
    ) []
    let cov := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
    result = cov ∧
    ∀ j < intervals.length,
      let rem_j := List.eraseIdx intervals j
      let sort_j := List.mergeSort rem_j (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged_j := sort_j.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let cov_j := merged_j.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      cov ≥ cov_j

end VerinaSpec

namespace LLMSpec

-- Remove the element at index i, keeping all other elements in order.
-- Defined using take/drop (non-recursive).
def removeAt (intervals : List (Prod Nat Nat)) (i : Nat) : List (Prod Nat Nat) :=
  intervals.take i ++ intervals.drop (i + 1)

-- Minimum left endpoint of a non-empty interval list.
def minLeftOfNonempty (intervals : List (Prod Nat Nat)) : Nat :=
  match intervals with
  | [] => 0
  | h :: t =>
      t.foldl (fun (acc : Nat) (p : Prod Nat Nat) => Nat.min acc p.1) (init := h.1)

-- Maximum right endpoint of a non-empty interval list.
def maxRightOfNonempty (intervals : List (Prod Nat Nat)) : Nat :=
  match intervals with
  | [] => 0
  | h :: t =>
      t.foldl (fun (acc : Nat) (p : Prod Nat Nat) => Nat.max acc p.2) (init := h.2)

-- Span of an interval list. Empty list span is 0.
def span (intervals : List (Prod Nat Nat)) : Nat :=
  match intervals with
  | [] => 0
  | _ :: _ =>
      (maxRightOfNonempty intervals) - (minLeftOfNonempty intervals)

-- Interval well-formedness: l ≤ r.
def intervalWellFormed (p : Prod Nat Nat) : Prop :=
  p.1 ≤ p.2

-- Preconditions
-- 1) At least one interval is provided.
-- 2) Every interval is well-formed.
def precondition (intervals : List (Prod Nat Nat)) : Prop :=
  intervals.length > 0 ∧
  ∀ p : Prod Nat Nat, p ∈ intervals → intervalWellFormed p

-- Postcondition: result is the maximum span achievable by removing exactly one interval.
-- Achievability: result is attained by removing some valid index.
-- Maximality: result is at least as large as the span produced by removing any valid index.
def postcondition (intervals : List (Prod Nat Nat)) (result : Nat) : Prop :=
  (∃ i : Nat, i < intervals.length ∧ span (removeAt intervals i) = result) ∧
  (∀ i : Nat, i < intervals.length → span (removeAt intervals i) ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (intervals : List (Prod Nat Nat)) :
  VerinaSpec.maxCoverageAfterRemovingOne_precond intervals ↔ LLMSpec.precondition intervals := by
  sorry

theorem postcondition_equiv (intervals : List (Prod Nat Nat)) (result: Nat) :
  LLMSpec.precondition intervals →
  (VerinaSpec.maxCoverageAfterRemovingOne_postcond intervals result ↔ LLMSpec.postcondition intervals result) := by
  sorry

end Proof
