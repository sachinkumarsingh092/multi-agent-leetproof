import Mathlib

section Specs

/- The original definition below is incorrect due to operator precedence.
   In Lean 4, `↔` (precedence 20) binds more loosely than `→` (precedence 25), so
     i < s.length → j < s.length → (s[i]! = s[j]!) ↔ (t[i]! = t[j]!)
   parses as
     (i < s.length → j < s.length → s[i]! = s[j]!) ↔ (t[i]! = t[j]!)
   which is NOT the intended meaning. -/
-- def Isomorphic (s : List Char) (t : List Char) : Prop :=
--   s.length = t.length ∧
--     ∀ (i : Nat) (j : Nat),
--       i < s.length → j < s.length →
--         (s[i]! = s[j]!) ↔ (t[i]! = t[j]!)

/-- Corrected definition: parentheses around the ↔ ensure the intended parsing. -/
def Isomorphic (s : List Char) (t : List Char) : Prop :=
  s.length = t.length ∧
    ∀ (i : Nat) (j : Nat),
      i < s.length → j < s.length →
        ((s[i]! = s[j]!) ↔ (t[i]! = t[j]!))

def precondition (s : List Char) (t : List Char) : Prop :=
  True

def postcondition (s : List Char) (t : List Char) (result : Bool) : Prop :=
  (result = true ↔ Isomorphic s t)
end Specs

lemma getD_eq_get! (l : List Char) (i : ℕ) :
    (l[i]?.getD 'A') = l[i]! := by
  by_cases h : i < l.length
  · simp [List.getElem?_eq_getElem h]
  · push_neg at h
    simp [List.getElem?_eq_none h]

/-
PROBLEM
Forward direction: ok_1 = true → Isomorphic

PROVIDED SOLUTION
Since done_1 says ¬(i_1 < s.length) and invariant_Iso_outer_i_bounds says i_1 ≤ s.length, we get i_1 = s.length (by omega or Nat.le_antisymm).

Unfold Isomorphic. Provide ⟨if_neg, ...⟩.

For the ∀ part: intro i j hi hj. Do rcases lt_trichotomy i j.

Case i < j: Use invariant_Iso_outer_checked i j (by omega) hj (the i < j hypothesis). This gives (s[i]?.getD 'A' = s[j]?.getD 'A') ↔ (t[i]?.getD 'A' = t[j]?.getD 'A'). Rewrite with getD_eq_get! (4 times, for s at i, s at j, t at i, t at j) to convert to s[i]! = s[j]! ↔ t[i]! = t[j]!.

Case i = j (rfl): Both sides of the iff are eq.refl, so simp or tauto closes it.

Case j < i: Use invariant_Iso_outer_checked j i (by omega) hi (the j < i hypothesis). This gives (s[j]?.getD 'A' = s[i]?.getD 'A') ↔ (t[j]?.getD 'A' = t[i]?.getD 'A'). Rewrite with getD_eq_get! to get s[j]! = s[i]! ↔ t[j]! = t[i]!. Then convert using eq_comm on both sides: constructor; intro h; exact (this.mp h.symm).symm; intro h; exact (this.mpr h.symm).symm.
-/
lemma goal_0_fwd
    (s t : List Char) (i_1 : ℕ)
    (if_neg : s.length = t.length)
    (invariant_Iso_outer_i_bounds : i_1 ≤ s.length)
    (invariant_Iso_outer_checked : ∀ (p q : ℕ), p < i_1 → q < s.length → p < q →
      ((s[p]?.getD 'A' = s[q]?.getD 'A') ↔ (t[p]?.getD 'A' = t[q]?.getD 'A')))
    (done_1 : ¬ (i_1 < s.length))
    : Isomorphic s t := by
  refine' ⟨ if_neg, fun i j hi hj => _ ⟩;
  grind +qlia

/-
PROBLEM
Backward direction: ok_1 = false → ¬ Isomorphic

PROVIDED SOLUTION
Obtain p, q, hpq, hq, habs from hcex. Suppose Isomorphic s t. Unfold Isomorphic to get hlen and hiso. Since p < q < s.length, p < s.length by omega. Specialize hiso at p, q to get s[p]! = s[q]! ↔ t[p]! = t[q]!. Rewrite with getD_eq_get! (4 times) in habs to convert the getD forms to get! forms. This gives ¬(s[p]! = s[q]! ↔ t[p]! = t[q]!). Contradiction.
-/
lemma goal_0_bwd
    (s t : List Char)
    (hcex : ∃ p q, p < q ∧ q < s.length ∧
      ¬((s[p]?.getD 'A' = s[q]?.getD 'A') ↔ (t[p]?.getD 'A' = t[q]?.getD 'A')))
    : ¬ Isomorphic s t := by
  -- By definition of Isomorphic, if there exist p and q such that the condition fails, then s and t cannot be isomorphic.
  obtain ⟨p, q, hpq, hq, habs⟩ := hcex
  by_contra h_iso
  obtain ⟨hlen, hiso⟩ := h_iso;
  grind +ring

theorem goal_0
    (s : List Char)
    (t : List Char)
    (require_1 : True)
    (i_1 : ℕ)
    (ok_1 : Bool)
    (if_neg : s.length = t.length)
    (invariant_Iso_outer_sizes : t.length = s.length)
    (invariant_Iso_outer_i_bounds : i_1 ≤ s.length)
    (invariant_Iso_outer_cex : ok_1 = false → ∃ p q, p < q ∧ q < s.length ∧ ¬(s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (invariant_Iso_outer_checked : ok_1 = true → ∀ (p q : ℕ), p < i_1 → q < s.length → p < q → (s[p]?.getD 'A' = s[q]?.getD 'A' ↔ t[p]?.getD 'A' = t[q]?.getD 'A'))
    (done_1 : i_1 < s.length → ok_1 = false)
    : postcondition s t ok_1 := by
  unfold postcondition
  cases hok : ok_1
  · -- ok_1 = false
    simp only [Bool.false_eq_true, false_iff]
    exact goal_0_bwd s t (invariant_Iso_outer_cex hok)
  · -- ok_1 = true
    simp only [true_iff]
    have hdone : ¬(i_1 < s.length) := by
      intro h; have := done_1 h; rw [hok] at this; exact absurd this (by simp)
    exact goal_0_fwd s t i_1 if_neg invariant_Iso_outer_i_bounds
      (invariant_Iso_outer_checked hok) hdone