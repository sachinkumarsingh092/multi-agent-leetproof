import Mathlib.Tactic

namespace VerinaSpec


def moveZeroes_precond (xs : List Int) : Prop :=
  True

def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt

def moveZeroes_postcond (xs : List Int) (result: List Int) : Prop :=
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧
  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧
  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length

end VerinaSpec

namespace LLMSpec

-- Helper: Bool predicate for “is non-zero” (for use with List.filter).
def isNonZeroB (x : Int) : Bool := x != 0

-- Helper: Bool predicate for “is zero” (for use with List.filter).
def isZeroB (x : Int) : Bool := x == 0

-- No input restrictions.
def precondition (xs : List Int) : Prop :=
  True

-- Property-based stable partition specification:
-- (a) length preserved
-- (b) all zeros are at the end (zeros form a suffix)
-- (c) multiset preserved via element counts
-- (d) order of non-zero elements preserved (as filtered subsequence equality)
def postcondition (xs : List Int) (result : List Int) : Prop :=
  result.length = xs.length ∧
  (∀ (i : Nat) (j : Nat), i < j → j < result.length → result[i]! = 0 → result[j]! = 0) ∧
  (∀ (x : Int), result.count x = xs.count x) ∧
  (result.filter isNonZeroB) = (xs.filter isNonZeroB)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) :
  VerinaSpec.moveZeroes_precond xs ↔ LLMSpec.precondition xs := by
  sorry

theorem postcondition_equiv (xs : List Int) (result: List Int) :
  LLMSpec.precondition xs →
  (VerinaSpec.moveZeroes_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  sorry

end Proof
