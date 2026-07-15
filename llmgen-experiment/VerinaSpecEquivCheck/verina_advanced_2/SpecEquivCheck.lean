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

-- `idxs` is a valid index embedding for witnessing that `sub` is a subsequence of `sup`.
-- Intuition: `idxs` lists the positions in `sup` from which we read out the elements of `sub`.

def ValidEmbedding (sub : Array Int) (sup : Array Int) (idxs : Array Nat) : Prop :=
  idxs.size = sub.size ∧
  (∀ i : Nat, i < idxs.size → idxs[i]! < sup.size) ∧
  (∀ i : Nat, i + 1 < idxs.size → idxs[i]! < idxs[i + 1]!) ∧
  (∀ i : Nat, i < sub.size → sub[i]! = sup[idxs[i]!]!)

-- `sub` is a subsequence of `sup`.
def IsSubsequence (sub : Array Int) (sup : Array Int) : Prop :=
  ∃ idxs : Array Nat, ValidEmbedding sub sup idxs

-- `c` is a common subsequence of `a` and `b`.
def IsCommonSubsequence (a : Array Int) (b : Array Int) (c : Array Int) : Prop :=
  IsSubsequence c a ∧ IsSubsequence c b

-- There are no restrictions on inputs.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  True

-- The result is the maximum achievable length among common subsequences.
-- We express maximality and existence using a witness length `k : Nat` and `result = Int.ofNat k`.

def postcondition (a : Array Int) (b : Array Int) (result : Int) : Prop :=
  (∃ k : Nat,
    result = Int.ofNat k ∧
    k ≤ Nat.min a.size b.size ∧
    (∃ c : Array Int, IsCommonSubsequence a b c ∧ c.size = k) ∧
    (∀ c : Array Int, IsCommonSubsequence a b c → c.size ≤ k))

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
