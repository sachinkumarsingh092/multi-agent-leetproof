import Mathlib.Tactic
import Mathlib.Data.List.Basic

namespace VerinaSpec


def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing if it is pairwise related by `<`.
-- This implies each element is < every later element, and in particular adjacent elements increase.
-- It also holds for [] and singletons.
def StrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (fun (a : Int) (b : Int) => a < b)

-- `List.Sublist sub nums` is the standard Mathlib relation for an order-preserving subsequence.
def IsIncSubseq (sub : List Int) (nums : List Int) : Prop :=
  List.Sublist sub nums ∧ StrictlyIncreasing sub

-- No input restrictions.
def precondition (nums : List Int) : Prop :=
  True

-- The result is the length of a longest strictly increasing subsequence:
-- (1) there exists an increasing subsequence with length exactly `result`
-- (2) every increasing subsequence has length at most `result`
def postcondition (nums : List Int) (result : Nat) : Prop :=
  (∃ sub : List Int, IsIncSubseq sub nums ∧ sub.length = result) ∧
  (∀ sub : List Int, IsIncSubseq sub nums → sub.length ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.longestIncreasingSubsequence_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Nat) :
  LLMSpec.precondition nums →
  (VerinaSpec.longestIncreasingSubsequence_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
