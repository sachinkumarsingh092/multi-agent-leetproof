/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 61c7e42c-10c8-4f40-b3c1-0548de6c55eb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.lengthOfLIS_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.lengthOfLIS_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

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

theorem precondition_equiv (nums : List Int) : VerinaSpec.lengthOfLIS_precond nums ↔ LLMSpec.precondition nums := by
  -- Since both preconditions are True, the equivalence is trivial.
  simp [VerinaSpec.lengthOfLIS_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.lengthOfLIS_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold LLMSpec.postcondition VerinaSpec.lengthOfLIS_postcond;
  -- The set of subsequences considered in the VerinaSpec definition is exactly the set of strictly increasing subsequences.
  have h_subseq : ∀ l : List ℤ, VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing l ↔ LLMSpec.isStrictlyIncreasing l := by
    intro l; exact (by
    unfold LLMSpec.isStrictlyIncreasing; induction' l with hd tl ih <;> simp_all +decide [ List.pairwise_cons ] ;
    cases tl <;> simp_all +decide [ VerinaSpec.lengthOfLIS_postcond.isStrictlyIncreasing ];
    exact fun h1 h2 h3 a ha => lt_trans h3 ( h1 a ha ));
  -- By definition of `subsequences`, we know that every subsequence in `subsequences nums` is a sublist of `nums`.
  have h_subseq_sublist : ∀ l : List ℤ, l ∈ VerinaSpec.lengthOfLIS_postcond.subsequences nums ↔ l.Sublist nums := by
    -- By definition of `subsequences`, we know that every subsequence in `subsequences nums` is a sublist of `nums`. We can prove this by induction on `nums`.
    have h_subseq_sublist_induction : ∀ nums : List ℤ, ∀ l : List ℤ, l ∈ VerinaSpec.lengthOfLIS_postcond.subsequences nums ↔ l.Sublist nums := by
      intro nums l; induction' nums with hd tl ih generalizing l <;> simp_all +decide [ List.sublist_cons_iff ] ;
      · cases l <;> simp +decide [ VerinaSpec.lengthOfLIS_postcond.subsequences ];
      · -- By definition of `subsequences`, we know that every subsequence in `subsequences (hd :: tl)` is either a subsequence of `tl` or `hd` followed by a subsequence of `tl`.
        have h_subseq_def : VerinaSpec.lengthOfLIS_postcond.subsequences (hd :: tl) = VerinaSpec.lengthOfLIS_postcond.subsequences tl ++ List.map (fun r => hd :: r) (VerinaSpec.lengthOfLIS_postcond.subsequences tl) := by
          exact?;
        aesop;
    exact h_subseq_sublist_induction nums;
  simp_all +decide [ LLMSpec.isIncSubseq ];
  grind

end Proof