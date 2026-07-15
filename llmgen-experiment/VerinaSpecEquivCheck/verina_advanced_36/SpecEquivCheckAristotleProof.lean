/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fabffb87-7450-4aee-a493-458266c524e3

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (xs : List Nat) : VerinaSpec.majorityElement_precond xs ↔ LLMSpec.precondition xs

- theorem postcondition_equiv (xs : List Nat) (result : Nat) : LLMSpec.precondition xs →
  (VerinaSpec.majorityElement_postcond xs result ↔ LLMSpec.postcondition xs result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def majorityElement_precond (xs : List Nat) : Prop :=
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)

def majorityElement_postcond (xs : List Nat) (result: Nat) : Prop :=
  let count := xs.count result
  count > xs.length / 2

end VerinaSpec

namespace LLMSpec

-- A value is a majority element of a list if it appears strictly more than half of the list length.
def IsMajority (xs : List Nat) (v : Nat) : Prop :=
  xs.count v > xs.length / 2

-- Precondition: a majority element exists (which also implies non-emptiness).
def precondition (xs : List Nat) : Prop :=
  ∃ m : Nat, IsMajority xs m

-- Postcondition: `result` is a majority element, and any majority element must equal `result`
-- (so the output is uniquely determined by the mathematical property).
def postcondition (xs : List Nat) (result : Nat) : Prop :=
  IsMajority xs result ∧
  (∀ y : Nat, IsMajority xs y → y = result)

end LLMSpec

section Proof

theorem precondition_equiv (xs : List Nat) : VerinaSpec.majorityElement_precond xs ↔ LLMSpec.precondition xs := by
  -- The two preconditions are equivalent because they both require the list to be non-empty and have a majority element.
  simp [VerinaSpec.majorityElement_precond, LLMSpec.precondition];
  -- If there exists an element m in xs such that the count of m is greater than half the length of xs, then obviously there exists such an m.
  apply Iff.intro
  intro h
  obtain ⟨m, hm⟩ := h.right
  use m
  exact hm.right
  intro h
  obtain ⟨m, hm⟩ := h
  exact ⟨by
  -- Since $m$ is a majority element, its count is greater than half the length of $xs$. If $xs$ were empty, then the count of $m$ would be zero, which contradicts $hm$. Therefore, $xs$ must have at least one element, making its length positive.
  by_contra h_empty;
  unfold LLMSpec.IsMajority at hm; aesop;, m, by
    exact ⟨ List.count_pos_iff.mp ( pos_of_gt hm ), hm ⟩⟩

theorem postcondition_equiv (xs : List Nat) (result : Nat) : LLMSpec.precondition xs →
  (VerinaSpec.majorityElement_postcond xs result ↔ LLMSpec.postcondition xs result) := by
  -- If the VerinaSpec condition holds, then by definition, there exists a majority element.
  intro h_precondition
  apply Iff.intro;
  · -- If the VerinaSpec postcondition holds, then by definition, the result is a majority element.
    intro h_verina
    apply And.intro h_verina;
    intro y hy
    by_contra hy_neq;
    have h_count : xs.count y + xs.count result ≤ xs.length := by
      have h_count : ∀ {l : List ℕ}, List.count y l + List.count result l ≤ l.length := by
        -- We can prove this by induction on the list.
        intro l
        induction' l with x l ih;
        · norm_num;
        · grind;
      apply h_count;
    unfold VerinaSpec.majorityElement_postcond LLMSpec.IsMajority at * ; omega;
  · exact fun h => h.1

end Proof