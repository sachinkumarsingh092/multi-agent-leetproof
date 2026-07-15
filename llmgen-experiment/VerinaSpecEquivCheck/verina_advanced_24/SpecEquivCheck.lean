import Mathlib.Tactic

namespace VerinaSpec


def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

def lengthOfLIS_postcond (nums : List Int) (result: Int) : Prop :=
  let rec isStrictlyIncreasing (l : List Int) : Bool :=
    match l with
    | [] | [_] => true
    | x :: y :: rest => x < y && isStrictlyIncreasing (y :: rest)
  let rec subsequences (xs : List Int) : List (List Int) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
      let rest := subsequences xs'
      rest ++ rest.map (fun r => x :: r)
  let allIncreasing := subsequences nums |>.filter (fun l => isStrictlyIncreasing l)
  allIncreasing.any (fun l => l.length = result) ∧
  allIncreasing.all (fun l => l.length ≤ result)

end VerinaSpec

namespace LLMSpec

-- A list is strictly increasing when all earlier elements are < all later elements.
-- For linear orders like Int, `Pairwise (· < ·)` captures this notion.
def isStrictlyIncreasing (l : List Int) : Prop :=
  l.Pairwise (fun a b => a < b)

-- A candidate list `s` is a valid strictly increasing subsequence of `nums`.
def isIncSubseq (nums : List Int) (s : List Int) : Prop :=
  s.Sublist nums ∧ isStrictlyIncreasing s

-- No preconditions: the result is defined for every input list.
def precondition (nums : List Int) : Prop :=
  True

-- The result is exactly the maximum length of a strictly increasing subsequence.
-- We phrase lengths as `Int.ofNat s.length` to match the required return type `Int`.
def postcondition (nums : List Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  (∃ s : List Int, isIncSubseq nums s ∧ Int.ofNat s.length = result) ∧
  (∀ t : List Int, isIncSubseq nums t → Int.ofNat t.length ≤ result)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) :
  VerinaSpec.lengthOfLIS_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Int) (result: Int) :
  LLMSpec.precondition nums →
  (VerinaSpec.lengthOfLIS_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
