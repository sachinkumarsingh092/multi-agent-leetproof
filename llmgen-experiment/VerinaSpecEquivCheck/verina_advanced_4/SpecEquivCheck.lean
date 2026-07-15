import Mathlib.Tactic
import Mathlib

namespace VerinaSpec


def LongestIncreasingSubsequence_precond (a : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestIncreasingSubsequence_postcond (a : Array Int) (result: Int) : Prop :=
  let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- Indices are valid positions within the array.
def idxsInBounds (a : Array Int) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k < idxs.size → idxs[k]! < a.size

-- Indices are strictly increasing (preserve order of the subsequence).
def idxsStrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (k : Nat), k + 1 < idxs.size → idxs[k]! < idxs[k + 1]!

-- Values picked by indices are strictly increasing.
def valsStrictlyIncreasing (a : Array Int) (idxs : Array Nat) : Prop :=
  ∀ (k : Nat),
    k + 1 < idxs.size →
      a[idxs[k]!]! < a[idxs[k + 1]!]!

-- A strictly increasing subsequence (represented by its index array).
def isStrictIncSubseqByIdxs (a : Array Int) (idxs : Array Nat) : Prop :=
  idxsInBounds a idxs ∧ idxsStrictlyIncreasing idxs ∧ valsStrictlyIncreasing a idxs

-- No input restriction: LIS length exists for all arrays.
def precondition (a : Array Int) : Prop :=
  True

-- result is the maximum possible length of any strictly increasing subsequence.
def postcondition (a : Array Int) (result : Int) : Prop :=
  0 ≤ result ∧
  result ≤ Int.ofNat a.size ∧
  (∃ (idxs : Array Nat), isStrictIncSubseqByIdxs a idxs ∧ Int.ofNat idxs.size = result) ∧
  (∀ (idxs : Array Nat), isStrictIncSubseqByIdxs a idxs → Int.ofNat idxs.size ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) :
  VerinaSpec.LongestIncreasingSubsequence_precond a ↔ LLMSpec.precondition a := by
  sorry

theorem postcondition_equiv (a : Array Int) (result: Int) :
  LLMSpec.precondition a →
  (VerinaSpec.LongestIncreasingSubsequence_postcond a result ↔ LLMSpec.postcondition a result) := by
  sorry

end Proof
