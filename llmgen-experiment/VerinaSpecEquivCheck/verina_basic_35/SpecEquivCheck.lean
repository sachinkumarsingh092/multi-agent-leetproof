import Mathlib.Tactic

namespace VerinaSpec


def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  True

def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)

end VerinaSpec

namespace LLMSpec

-- Helper: count of non-zero elements.
-- We use Bool predicates for computable counting via `Array.countP`.
def nonZeroCount (arr : Array Int) : Nat :=
  arr.countP (fun x => x != 0)

-- Helper: the number of non-zero elements strictly before index `i`.
-- This is the “rank” of the element at `i` among non-zero elements.
def nzRank (arr : Array Int) (i : Nat) : Nat :=
  (arr.take i).countP (fun x => x != 0)

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- Size is preserved.
  result.size = arr.size ∧
  -- The number of zeros is preserved.
  result.countP (fun x => x == 0) = arr.countP (fun x => x == 0) ∧
  -- Zeros form a suffix (all indices at/after `k` are 0, and before `k` are non-zero).
  (let k := nonZeroCount arr
   (∀ i : Nat, i < k → result[i]! ≠ 0) ∧
   (∀ i : Nat, k ≤ i → i < result.size → result[i]! = 0)) ∧
  -- Stability for non-zero elements:
  -- For every non-zero element at position `j` in the input, it appears in the output at
  -- index `nzRank arr j`.
  (∀ j : Nat, j < arr.size → arr[j]! ≠ 0 →
    (let r := nzRank arr j
     r < result.size ∧ result[r]! = arr[j]!)) ∧
  -- Coverage of all non-zero output positions:
  -- Every index in the non-zero prefix corresponds to some non-zero element of the input
  -- with the same rank.
  (let k := nonZeroCount arr
   ∀ i : Nat, i < k →
     ∃ j : Nat, j < arr.size ∧ arr[j]! ≠ 0 ∧ nzRank arr j = i ∧ result[i]! = arr[j]!)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) :
  VerinaSpec.MoveZeroesToEnd_precond arr ↔ LLMSpec.precondition arr := by
  sorry

theorem postcondition_equiv (arr : Array Int) (result: Array Int) :
  LLMSpec.precondition arr →
  (VerinaSpec.MoveZeroesToEnd_postcond arr result ↔ LLMSpec.postcondition arr result) := by
  sorry

end Proof
