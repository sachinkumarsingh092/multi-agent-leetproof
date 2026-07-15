import Mathlib.Tactic
import Mathlib

namespace VerinaSpec


def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  True

def longestIncreasingSubsequence_postcond (numbers : List Int) (result: Nat) : Prop :=
  let allSubseq := (numbers.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing when all pairs of positions are strictly ordered.
-- `Pairwise (· < ·)` implies in particular that adjacent elements are strictly increasing.
def isStrictlyIncreasing (xs : List Int) : Prop :=
  xs.Pairwise (fun a b => a < b)

-- A subsequence relation: `xs` is a subsequence of `numbers` if it can be obtained
-- by deleting elements from `numbers` without reordering.
-- In this library setup, `List.Sublist` is the available relation for this notion.
def isSubsequence (xs : List Int) (numbers : List Int) : Prop :=
  List.Sublist xs numbers

def precondition (numbers : List Int) : Prop :=
  True

def postcondition (numbers : List Int) (result : Nat) : Prop :=
  (∃ (s : List Int),
      isSubsequence s numbers ∧
      isStrictlyIncreasing s ∧
      s.length = result) ∧
  (∀ (t : List Int),
      isSubsequence t numbers →
      isStrictlyIncreasing t →
      t.length ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (numbers : List Int) :
  VerinaSpec.longestIncreasingSubsequence_precond numbers ↔ LLMSpec.precondition numbers := by
  sorry

theorem postcondition_equiv (numbers : List Int) (result: Nat) :
  LLMSpec.precondition numbers →
  (VerinaSpec.longestIncreasingSubsequence_postcond numbers result ↔ LLMSpec.postcondition numbers result) := by
  sorry

end Proof
