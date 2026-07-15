/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7e2106f6-3e90-468a-9971-f2920275067d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) : VerinaSpec.longestIncreasingSubseqLength_precond xs ↔ LLMSpec.precondition xs

- theorem postcondition_equiv (xs : List Int) (result : Nat) : LLMSpec.precondition xs →
  (VerinaSpec.longestIncreasingSubseqLength_postcond xs result ↔ LLMSpec.postcondition xs result)
-/

import Mathlib.Tactic

import Mathlib.Data.List.Basic


namespace VerinaSpec

def longestIncreasingSubseqLength_precond (xs : List Int) : Prop :=
  True

def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences xs
    subs ++ subs.map (fun s => x :: s)

def isStrictlyIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => if x < y then isStrictlyIncreasing (y :: rest) else false

def longestIncreasingSubseqLength_postcond (xs : List Int) (result: Nat) : Prop :=
  let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: `ys` is a strictly increasing subsequence of `xs`.
-- `List.Sublist` captures the subsequence notion (delete elements, preserve order).
-- `Pairwise (fun a b => a < b)` captures strict increase across all earlier/later pairs.
def isStrictIncSubseq (xs : List Int) (ys : List Int) : Prop :=
  List.Sublist ys xs ∧ ys.Pairwise (fun a b => a < b)

-- No preconditions: LIS length is defined for all lists.
def precondition (xs : List Int) : Prop :=
  True

-- Postcondition: `result` is the length of a longest strictly increasing subsequence.
-- 1) Upper bound: every strictly increasing subsequence has length ≤ result.
-- 2) Achievability: there exists a strictly increasing subsequence whose length is exactly result.
def postcondition (xs : List Int) (result : Nat) : Prop :=
  (∀ (ys : List Int), isStrictIncSubseq xs ys → ys.length ≤ result) ∧
  (∃ (ys : List Int), isStrictIncSubseq xs ys ∧ ys.length = result)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) : VerinaSpec.longestIncreasingSubseqLength_precond xs ↔ LLMSpec.precondition xs := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.longestIncreasingSubseqLength_precond, LLMSpec.precondition]

theorem postcondition_equiv (xs : List Int) (result : Nat) : LLMSpec.precondition xs →
  (VerinaSpec.longestIncreasingSubseqLength_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  unfold LLMSpec.precondition VerinaSpec.longestIncreasingSubseqLength_postcond LLMSpec.postcondition;
  -- To prove the equivalence, we can show that the two conditions are equivalent by definition.
  simp [LLMSpec.isStrictIncSubseq];
  -- To prove the equivalence, we can show that the two conditions are equivalent by definition of `List.foldl`.
  have h_foldl : ∀ (xs : List ℤ), List.foldl (fun (acc : List (List ℤ)) (x : ℤ) => acc ++ List.map (fun (sub : List ℤ) => x :: sub) acc) [[]] xs = List.map (fun (sub : List ℤ) => sub.reverse) (List.sublists xs) := by
    intro xs; induction' xs using List.reverseRecOn with xs ih <;> simp_all +decide [ List.sublists_cons ] ;
  constructor <;> intro h <;> simp_all +decide [ List.pairwise_reverse ];
  · exact fun ys hy hy' => Or.resolve_left ( h.2 ys hy ) ( by aesop );
  · grind +ring

end Proof