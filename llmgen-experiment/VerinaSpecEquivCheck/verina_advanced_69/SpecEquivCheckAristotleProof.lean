/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8b9c1270-8f7c-4603-b820-c9e3c9e91214

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Int) (target : Int) : VerinaSpec.searchInsert_precond xs target ↔ LLMSpec.precondition xs target

- theorem postcondition_equiv (xs : List Int) (target : Int) (result : Nat) : LLMSpec.precondition xs target →
  (VerinaSpec.searchInsert_postcond xs target result ↔ LLMSpec.postcondition xs target result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  List.Pairwise (· < ·) xs

def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) : Prop :=
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly

end VerinaSpec

namespace LLMSpec

-- Helper predicate: xs is strictly increasing.
def StrictInc (xs : List Int) : Prop :=
  xs.Chain' (fun a b => a < b)

-- Lower-bound style characterization of the insertion point.
def precondition (xs : List Int) (target : Int) : Prop :=
  StrictInc xs

def postcondition (xs : List Int) (target : Int) (result : Nat) : Prop :=
  result ≤ xs.length ∧
  (∀ (i : Nat), i < result → xs[i]! < target) ∧
  (∀ (i : Nat), result ≤ i → i < xs.length → target ≤ xs[i]!)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Int) (target : Int) : VerinaSpec.searchInsert_precond xs target ↔ LLMSpec.precondition xs target := by
  -- The pairwise condition and the chain condition are equivalent because they both state that the list is strictly increasing.
  apply Iff.intro;
  · -- If the list is pairwise strictly increasing, then it is strictly increasing.
    intros h_pairwise
    apply List.Pairwise.chain' h_pairwise;
  · -- By definition of StrictInc, if StrictInc xs holds, then for any two consecutive elements in the list, the first is less than the second.
    intro h_strict_inc
    apply List.isChain_iff_pairwise.mp h_strict_inc

theorem postcondition_equiv (xs : List Int) (target : Int) (result : Nat) : LLMSpec.precondition xs target →
  (VerinaSpec.searchInsert_postcond xs target result ↔ LLMSpec.postcondition xs target result) := by
  -- By definition of `List.range`, we know that `List.range result` is exactly the set of indices less than `result`.
  have h_range : ∀ (result : ℕ), (List.range result).all (fun i => xs[i]! < target) ↔ ∀ i < result, xs[i]! < target := by
    grind;
  -- By definition of `List.range`, we know that `List.range result` is exactly the set of indices less than `result`. Therefore, the two postconditions are equivalent.
  simp [VerinaSpec.searchInsert_postcond, LLMSpec.postcondition, h_range];
  -- To prove the equivalence, we can split into two implications.
  intro h_precond h_result h_all_before
  constructor;
  · intro h i hi₁ hi₂;
    -- By induction on $i$, we can show that for any $i \geq result$, $xs[i]! \geq target$.
    induction' hi₁ with i hi ih;
    · exact h hi₂;
    · have := List.isChain_iff_get.mp h_precond;
      grind;
  · exact fun h _ => h _ le_rfl ‹_›

end Proof