import Mathlib.Tactic

namespace VerinaSpec


def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- Helper: strictly increasing indices for an index array.
def StrictlyIncreasing (idxs : Array Nat) : Prop :=
  ∀ (j : Nat), j + 1 < idxs.size → idxs[j]! < idxs[j + 1]!

-- Helper: s is a subsequence of arr, witnessed by an index array idxs.
def SubseqWitness (s : Array Int) (arr : Array Int) (idxs : Array Nat) : Prop :=
  idxs.size = s.size ∧
  StrictlyIncreasing idxs ∧
  (∀ (j : Nat), j < s.size → idxs[j]! < arr.size ∧ s[j]! = arr[idxs[j]!]!)

-- Helper: array subsequence relation.
def IsSubsequence (s : Array Int) (arr : Array Int) : Prop :=
  ∃ (idxs : Array Nat), SubseqWitness s arr idxs

-- Precondition: no restrictions on inputs.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- Postcondition: result is the maximum possible length of any common subsequence.
-- Note: result is Int, but array sizes are Nat, so we relate them via Int.ofNat and result.toNat.
def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ (s : Array Int), IsSubsequence s a ∧ IsSubsequence s b ∧ result = Int.ofNat s.size) ∧
  (∀ (t : Array Int), IsSubsequence t a ∧ IsSubsequence t b → (Int.ofNat t.size) ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) :
  VerinaSpec.LongestCommonSubsequence_precond a b ↔ LLMSpec.precondition a b := by
  sorry

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result: Int) :
  LLMSpec.precondition a b →
  (VerinaSpec.LongestCommonSubsequence_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  sorry

end Proof
