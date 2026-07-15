import Mathlib.Tactic

namespace VerinaSpec


def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  k > 0

def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k.toNat = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.toList.sum)
  (subarraySums.length = 0 → result = 0) ∧
  (subarraySums.length > 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))

end VerinaSpec

namespace LLMSpec

-- Convert the (positive) Int k to Nat for divisibility over Nat lengths.
-- Precondition guarantees 2 ≤ k, so Int.toNat k is nonzero.
def kNat (k : Int) : Nat :=
  Int.toNat k

-- Sum of the subarray arr[start:stop] (stop exclusive).
-- We use Array.extract, together with explicit bounds in predicates, to model a subarray slice.
def subarraySum (arr : Array Int) (start : Nat) (stop : Nat) : Int :=
  (arr.extract start stop).sum

-- A non-empty, in-bounds subarray.
def validSubarray (arr : Array Int) (start : Nat) (stop : Nat) : Prop :=
  start < stop ∧ stop ≤ arr.size

-- Length divisibility by k (with k viewed as a natural number).
def lenDivisibleByK (len : Nat) (k : Int) : Prop :=
  len % (kNat k) = 0

-- Candidate predicate: a valid non-empty subarray with length divisible by k.
def isCandidate (arr : Array Int) (k : Int) (start : Nat) (stop : Nat) : Prop :=
  validSubarray arr start stop ∧ lenDivisibleByK (stop - start) k

-- k must be larger than 1.
def precondition (arr : Array Int) (k : Int) : Prop :=
  2 ≤ k

-- result is the greatest nonnegative sum among all candidate subarrays; default 0.
def postcondition (arr : Array Int) (k : Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∀ (start : Nat) (stop : Nat), isCandidate arr k start stop → subarraySum arr start stop ≤ result) ∧
  (result = 0 ∨ ∃ (start : Nat) (stop : Nat), isCandidate arr k start stop ∧ subarraySum arr start stop = result)

end LLMSpec

section Proof

theorem precondition_equiv (arr : Array Int) (k : Int) :
  VerinaSpec.maxSubarraySumDivisibleByK_precond arr k ↔ LLMSpec.precondition arr k := by
  sorry

theorem postcondition_equiv (arr : Array Int) (k : Int) (result: Int) :
  LLMSpec.precondition arr k →
  (VerinaSpec.maxSubarraySumDivisibleByK_postcond arr k result ↔ LLMSpec.postcondition arr k result) := by
  sorry

end Proof
