/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d1ae7447-c669-4453-8d88-c350c82ef61d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int) : VerinaSpec.findMajorityElement_precond lst ↔ LLMSpec.precondition lst

- theorem postcondition_equiv (lst : List Int) (result : Int) : LLMSpec.precondition lst →
  (VerinaSpec.findMajorityElement_postcond lst result ↔ LLMSpec.postcondition lst result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def findMajorityElement_precond (lst : List Int) : Prop :=
  True

def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

def findMajorityElement_postcond (lst : List Int) (result: Int) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: x is a majority element of lst iff it appears strictly more than half the time.
-- We avoid division by using the equivalent inequality 2 * count(x) > length.
-- Note: `lst.count x : Nat` and `lst.length : Nat`.
def isMajority (lst : List Int) (x : Int) : Prop :=
  (2 * lst.count x) > lst.length

def precondition (lst : List Int) : Prop :=
  True

-- Postcondition:
-- 1. If a majority element exists, `result` is that unique majority element.
-- 2. If no majority element exists, `result = -1`.
-- This matches the prompt's requirement "return the majority element if one exists, otherwise -1".
def postcondition (lst : List Int) (result : Int) : Prop :=
  ((∃ x : Int, isMajority lst x) →
      (isMajority lst result ∧ ∀ x : Int, isMajority lst x → x = result)) ∧
  ((¬ (∃ x : Int, isMajority lst x)) → result = (-1))

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) : VerinaSpec.findMajorityElement_precond lst ↔ LLMSpec.precondition lst := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.findMajorityElement_precond, LLMSpec.precondition]

theorem postcondition_equiv (lst : List Int) (result : Int) : LLMSpec.precondition lst →
  (VerinaSpec.findMajorityElement_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  -- By definition of `VerinaSpec.findMajorityElement_postcond` and `LLMSpec.postcondition`, we can show that they are equivalent.
  simp [VerinaSpec.findMajorityElement_postcond, LLMSpec.postcondition];
  intro h_pre
  constructor
  intro h_no_majority
  by_cases h_result : result = -1 <;> simp_all +decide [ LLMSpec.isMajority ];
  · intro x hx; have := h_no_majority; rcases this with ( h | h ) <;> simp_all +decide [ List.filter_eq ] ;
    · exact absurd ( h x ( by contrapose! hx; simp_all +decide [ List.count_eq_zero_of_not_mem ] ) ) ( by omega );
    · exact ⟨ by omega, fun x hx => by have := h.2 x ( List.count_pos_iff.mp ( by linarith ) ) ; omega ⟩;
  · -- If x is a majority element, then by h_no_majority, x must equal result.
    have h_majority : ∀ x, lst.length < 2 * List.count x lst → x = result := by
      intros x hx
      by_cases hx_mem : x ∈ lst;
      · cases h_no_majority.2 x hx_mem <;> simp_all +decide [ List.filter_eq ];
        omega;
      · simp_all +decide [ List.count_eq_zero_of_not_mem ];
    refine' ⟨ fun x hx => ⟨ _, h_majority ⟩, _ ⟩;
    · rw [ ← h_majority x hx ] ; linarith;
    · use result; simp_all +decide [ List.filter_eq ] ; omega;
  · intro h
    by_cases h_result : result = -1 <;> simp_all +decide [ LLMSpec.isMajority ];
    · by_cases h_exists_majority : ∃ x ∈ lst, lst.length < 2 * List.count x lst <;> simp_all +decide [ List.filter_eq ];
      · grind;
      · exact Or.inl fun x hx => by linarith [ h_exists_majority x hx, Nat.div_add_mod lst.length 2, Nat.mod_lt lst.length two_pos ] ;
    · obtain ⟨ x, hx ⟩ := h.2; have := h.1 x hx; simp_all +decide [ List.filter_eq ] ;
      grind +ring

end Proof