import Mathlib.Tactic

namespace VerinaSpec


def task_code_precond (sequence : List Int) : Prop :=
  sequence.length > 0  -- At least one element must be selected

def task_code_postcond (sequence : List Int) (result: Int) : Prop :=
  let subArrays :=
    List.range (sequence.length + 1) |>.flatMap (fun start =>
      List.range (sequence.length - start + 1) |>.map (fun len =>
        sequence.drop start |>.take len))
  let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum)
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- Helper: sum of a list of integers.
-- We use `foldl` to avoid relying on any particular `List.sum` import.
def listSum (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc + x) 0

-- Helper: contiguous subarray slice of `sequence` from `start` (inclusive) to `stop` (exclusive).
-- Intended use is with `start < stop` and `stop ≤ sequence.length`.
def subarraySlice (sequence : List Int) (start : Nat) (stop : Nat) : List Int :=
  (sequence.drop start).take (stop - start)

-- Helper: sum of a contiguous subarray slice.
def subarraySliceSum (sequence : List Int) (start : Nat) (stop : Nat) : Int :=
  listSum (subarraySlice sequence start stop)

-- Helper: (start, stop) denotes a valid non-empty contiguous subarray.
def isValidWindow (sequence : List Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ sequence.length

-- Preconditions
-- The input sequence must be non-empty.
def precondition (sequence : List Int) : Prop :=
  sequence.length > 0

-- Postconditions
-- `result` is the maximum sum among all non-empty contiguous subarrays.
def postcondition (sequence : List Int) (result : Int) : Prop :=
  (∃ (start : Nat) (stop : Nat),
      isValidWindow sequence start stop ∧
      subarraySliceSum sequence start stop = result) ∧
  (∀ (start : Nat) (stop : Nat),
      isValidWindow sequence start stop →
      subarraySliceSum sequence start stop ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (sequence : List Int) :
  VerinaSpec.task_code_precond sequence ↔ LLMSpec.precondition sequence := by
  sorry

theorem postcondition_equiv (sequence : List Int) (result: Int) :
  LLMSpec.precondition sequence →
  (VerinaSpec.task_code_postcond sequence result ↔ LLMSpec.postcondition sequence result) := by
  sorry

end Proof
