/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5ca56dcc-d6e8-425c-bc02-3c46515f3c9f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (sequence : List Int) : VerinaSpec.task_code_precond sequence ↔ LLMSpec.precondition sequence

- theorem postcondition_equiv (sequence : List Int) (result : Int) : LLMSpec.precondition sequence →
  (VerinaSpec.task_code_postcond sequence result ↔ LLMSpec.postcondition sequence result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def task_code_precond (sequence : List Int) : Prop :=
  sequence.length > 0

-- At least one element must be selected

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

theorem precondition_equiv (sequence : List Int) : VerinaSpec.task_code_precond sequence ↔ LLMSpec.precondition sequence := by
  -- The two preconditions are equivalent because they both state that the length of the sequence is greater than zero.
  simp [VerinaSpec.task_code_precond, LLMSpec.precondition]

theorem postcondition_equiv (sequence : List Int) (result : Int) : LLMSpec.precondition sequence →
  (VerinaSpec.task_code_postcond sequence result ↔ LLMSpec.postcondition sequence result) := by
  -- To prove the equivalence, we split into the two directions of the postcondition.
  intro h_precondition
  constructor;
  · -- If the VerinaSpec's postcondition holds, then there exists a subarray (start, stop) where the sum is equal to the result. This subarray is valid because it's non-empty and within the sequence's length.
    intro hVerina
    obtain ⟨subArray, hSubArray⟩ : ∃ subArray : List Int, subArray ∈ List.filter (· ≠ []) (List.flatMap (fun start => List.map (fun len => List.take len (List.drop start sequence)) (List.range (sequence.length - start + 1))) (List.range (sequence.length + 1))) ∧ subArray.sum = result := by
      unfold VerinaSpec.task_code_postcond at hVerina; aesop;
    obtain ⟨start, len, hStart, hLen⟩ : ∃ start len, start < start + len ∧ start + len ≤ sequence.length ∧ subArray = List.take len (List.drop start sequence) := by
      simp +zetaDelta at *;
      rcases hSubArray.1.1 with ⟨ start, hstart, len, hlen, rfl ⟩ ; exact ⟨ start, len, Nat.pos_of_ne_zero ( by aesop ), by omega, rfl ⟩ ;
    constructor;
    · use start, start + len;
      -- By definition of `subarraySliceSum`, we have `subarraySliceSum sequence start (start + len) = List.sum (List.take len (List.drop start sequence))`.
      simp [LLMSpec.subarraySliceSum, hLen];
      simp_all +decide [ LLMSpec.isValidWindow, LLMSpec.subarraySlice ];
      convert hSubArray.2 using 1;
      unfold LLMSpec.listSum; simp +decide [ List.sum_eq_foldl ] ;
    · intro start stop hWindow
      obtain ⟨hStart, hStop⟩ := hWindow
      have hSubarray : List.take (stop - start) (List.drop start sequence) ∈ List.filter (· ≠ []) (List.flatMap (fun start => List.map (fun len => List.take len (List.drop start sequence)) (List.range (sequence.length - start + 1))) (List.range (sequence.length + 1))) := by
        simp +zetaDelta at *;
        exact ⟨ ⟨ start, by linarith, stop - start, by omega, rfl ⟩, Nat.sub_ne_zero_of_lt ‹_›, by linarith ⟩;
      have := hVerina.2;
      simp_all +decide [ List.all_eq_true ];
      convert this start ( by linarith ) ( stop - start ) ( by omega ) |> Or.resolve_left <| by omega using 1;
      -- By definition of `subarraySliceSum`, we have `subarraySliceSum sequence start stop = List.sum (List.take (stop - start) (List.drop start sequence))`.
      simp [LLMSpec.subarraySliceSum, LLMSpec.subarraySlice];
      unfold LLMSpec.listSum; simp +decide [ List.sum_eq_foldl ] ;
  · intro h_postcondition;
    -- By definition of `postcondition`, we know that there exists a valid window (start, stop) such that the sum of the subarray from start to stop is equal to result, and for all valid windows, their sums are less than or equal to result.
    obtain ⟨start, stop, h_valid, h_sum⟩ := h_postcondition.left
    have h_all_le : ∀ (start' stop' : Nat), LLMSpec.isValidWindow sequence start' stop' → LLMSpec.subarraySliceSum sequence start' stop' ≤ result := by
      exact h_postcondition.2;
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ LLMSpec.subarraySliceSum, LLMSpec.subarraySlice ];
    · refine' ⟨ _, ⟨ ⟨ start, _, stop - start, _, rfl ⟩, _ ⟩, _ ⟩ <;> simp_all +decide [ LLMSpec.isValidWindow ];
      · linarith;
      · omega;
      · exact ⟨ Nat.sub_ne_zero_of_lt h_valid.1, h_valid.1.trans_le h_valid.2 ⟩;
      · convert h_sum using 1;
        unfold LLMSpec.listSum; simp +decide [ List.sum_eq_foldl ] ;
    · -- Let's split into cases based on whether x_1 is zero or not.
      intros x hx x_1 hx_1
      by_cases hx1 : x_1 = 0 ∨ sequence.length ≤ x;
      · tauto;
      · exact Or.inr ( by simpa [ List.sum_eq_foldl ] using h_all_le x ( x + x_1 ) ⟨ by omega, by omega ⟩ )

end Proof