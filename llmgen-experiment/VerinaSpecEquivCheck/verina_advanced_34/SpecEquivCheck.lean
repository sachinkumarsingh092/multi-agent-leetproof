import Mathlib.Tactic
import Mathlib.Data.List.Basic

namespace VerinaSpec


def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing iff every element is strictly less than every later element.
-- `List.Pairwise r xs` means `r` holds for every pair of elements with increasing position.
def StrictlyIncreasing (xs : List Int) : Prop :=
  xs.Pairwise (fun a => fun b => a < b)

-- `k` is the length (Nat) of a longest strictly increasing subsequence of `nums`.
-- We use `List.Sublist` as the subsequence relation (delete elements, order preserved).
-- Note: `[]` is a sublist of any list, so existence is always satisfied with `k = 0`.
def IsLISLengthNat (nums : List Int) (k : Nat) : Prop :=
  (∃ s : List Int, List.Sublist s nums ∧ StrictlyIncreasing s ∧ s.length = k) ∧
  (∀ t : List Int, List.Sublist t nums → StrictlyIncreasing t → t.length ≤ k)

-- No preconditions: any integer list is allowed.
def precondition (nums : List Int) : Prop :=
  True

-- The returned integer is the natural number `k` (encoded via `Int.ofNat`) such that:
-- 1) there exists a strictly increasing subsequence of length `k`, and
-- 2) no strictly increasing subsequence is longer than `k`.
def postcondition (nums : List Int) (result : Int) : Prop :=
  ∃ k : Nat,
    result = Int.ofNat k ∧
    IsLISLengthNat nums k

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.longestIncreasingSubsequence_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Int) :
  LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingSubsequence_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
