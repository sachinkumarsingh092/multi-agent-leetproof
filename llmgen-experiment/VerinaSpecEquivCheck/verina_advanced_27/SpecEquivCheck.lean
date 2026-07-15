import Mathlib.Tactic

namespace VerinaSpec


def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  True
partial def toCharList (s : String) : List Char :=
  s.data
partial def fromCharList (cs : List Char) : String :=
  cs.foldl (fun acc c => acc.push c) ""
partial def lcsAux (xs : List Char) (ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
    if x == y then
      x :: lcsAux xs' ys'
    else
      let left  := lcsAux xs' (y :: ys')
      let right := lcsAux (x :: xs') ys'
      if left.length >= right.length then left else right

def longestCommonSubsequence_postcond (s1 : String) (s2 : String) (result: String) : Prop :=
  let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq s1.toList
  let subseqB := allSubseq s2.toList
  let commonSubseq := subseqA.filter (fun l => subseqB.contains l)
  commonSubseq.contains result.toList ∧ commonSubseq.all (fun l => l.length ≤ result.length)

end VerinaSpec

namespace LLMSpec

-- Helper definitions

-- `isSubseqList r s` means `r` is a subsequence of `s`.
-- It is witnessed by an order-preserving index mapping from positions of `r` to positions of `s`.
-- We use natural-number indexing via `List.get!` (safe because we require the indices are in range).
--
-- Note: This definition avoids depending on any particular library name for subsequence.
-- It also avoids mixing `Array` and `List` in specifications; we specify everything over `List Char`.
def isSubseqList (r : List Char) (s : List Char) : Prop :=
  ∃ f : Nat → Nat,
    (∀ (i : Nat), i < r.length → f i < s.length) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < r.length → f i < f j) ∧
    (∀ (i : Nat), i < r.length → r.get! i = s.get! (f i))

def isCommonSubseqList (s1 : List Char) (s2 : List Char) (r : List Char) : Prop :=
  isSubseqList r s1 ∧ isSubseqList r s2

-- `r` is a longest common subsequence iff it is a common subsequence and
-- no other common subsequence is longer.
def isLCSList (s1 : List Char) (s2 : List Char) (r : List Char) : Prop :=
  isCommonSubseqList s1 s2 r ∧
  ∀ (t : List Char), isSubseqList t s1 → isSubseqList t s2 → t.length ≤ r.length

-- No input restrictions.
def precondition (s1 : String) (s2 : String) : Prop :=
  True

def postcondition (s1 : String) (s2 : String) (result : String) : Prop :=
  isLCSList s1.data s2.data result.data

end LLMSpec

section Proof

theorem precondition_equiv (s1 : String) (s2 : String) :
  VerinaSpec.longestCommonSubsequence_precond s1 s2 ↔ LLMSpec.precondition s1 s2 := by
  sorry

theorem postcondition_equiv (s1 : String) (s2 : String) (result: String) :
  LLMSpec.precondition s1 s2 →
  (VerinaSpec.longestCommonSubsequence_postcond s1 s2 result ↔ LLMSpec.postcondition s1 s2 result) := by
  sorry

end Proof
