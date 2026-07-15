/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6146512d-c44f-493d-886a-2b76b3cf7c06

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int) : VerinaSpec.isPeakValley_precond lst ↔ LLMSpec.precondition lst

- theorem postcondition_equiv (lst : List Int) (result : Bool) : LLMSpec.precondition lst →
  (VerinaSpec.isPeakValley_postcond lst result ↔ LLMSpec.postcondition lst result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isPeakValley_precond (lst : List Int) : Prop :=
  True

def isPeakValley_postcond (lst : List Int) (result: Bool) : Prop :=
  let len := lst.length
  let validPeaks :=
    List.range len |>.filter (fun p =>
      1 ≤ p ∧ p < len - 1 ∧
      (List.range p).all (fun i =>
        lst[i]! < lst[i + 1]!
      ) ∧
      (List.range (len - 1 - p)).all (fun i =>
        lst[p + i]! > lst[p + i + 1]!
      )
    )
  (validPeaks != [] → result) ∧
  (validPeaks.length = 0 → ¬ result)

end VerinaSpec

namespace LLMSpec

-- Helper predicate: consecutive strict increase up to peak index p.
-- We require that for every i < p, the adjacent elements i and i+1 strictly increase.
-- The extra guard (i + 1 < lst.length) makes indexing safe for List.get!.
def StrictIncTo (lst : List Int) (p : Nat) : Prop :=
  ∀ (i : Nat), i < p → i + 1 < lst.length → lst[i]! < lst[i + 1]!

-- Helper predicate: consecutive strict decrease starting at peak index p.
-- For every i ≥ p (up to the last adjacent pair), the adjacent elements i and i+1 strictly decrease.
def StrictDecFrom (lst : List Int) (p : Nat) : Prop :=
  ∀ (i : Nat), p ≤ i → i + 1 < lst.length → lst[i]! > lst[i + 1]!

-- Core mathematical notion of a peak-valley list.
-- There exists an interior peak index p with a strict increase before it and strict decrease after it.
def PeakValley (lst : List Int) : Prop :=
  ∃ (p : Nat),
    0 < p ∧
    p + 1 < lst.length ∧
    StrictIncTo lst p ∧
    StrictDecFrom lst p

def precondition (lst : List Int) : Prop :=
  True

def postcondition (lst : List Int) (result : Bool) : Prop :=
  result = true ↔ PeakValley lst

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) : VerinaSpec.isPeakValley_precond lst ↔ LLMSpec.precondition lst := by
  -- Since both preconditions are defined as True, the equivalence is trivial.
  simp [VerinaSpec.isPeakValley_precond, LLMSpec.precondition]

theorem postcondition_equiv (lst : List Int) (result : Bool) : LLMSpec.precondition lst →
  (VerinaSpec.isPeakValley_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  rintro -;
  -- By definition of `isPeakValley_postcond` and `postcondition`, we can see that they are equivalent because they both check for the existence of a peak index `p` with the required properties.
  simp [VerinaSpec.isPeakValley_postcond, LLMSpec.postcondition];
  constructor <;> intro h;
  · constructor <;> intro h';
    · -- Since there exists a valid peak index `p`, we can use it to satisfy the conditions of `LLMSpec.PeakValley`.
      obtain ⟨p, hp⟩ : ∃ p, 1 ≤ p ∧ p < lst.length - 1 ∧ (∀ i < p, lst[i]! < lst[i + 1]!) ∧ (∀ i < lst.length - 1 - p, lst[p + i]! > lst[p + i + 1]!) := by
        contrapose! h; aesop;
      use p;
      -- Since $p < lst.length - 1$, we have $p + 1 < lst.length$.
      have h_len : p + 1 < lst.length := by
        omega;
      exact ⟨ hp.1, h_len, fun i hi hi' => hp.2.2.1 i hi, fun i hi hi' => hp.2.2.2 ( i - p ) ( by omega ) |> fun h => by simpa [ add_tsub_cancel_of_le hi ] using h ⟩;
    · obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ := h';
      refine' h.1 p ( by linarith ) ( by linarith ) ( by omega ) _ _;
      · intro x hx; specialize hp₃ x hx ( by linarith ) ; aesop;
      · intro x hx; specialize hp₄ ( p + x ) ( by linarith ) ( by omega ) ; aesop;
  · constructor;
    · -- If the conditions hold for some x, then we can use that x as the p in the PeakValley definition.
      intro x hx_lt hx_ge hx_lt' hx_inc hx_dec
      have h_peak : LLMSpec.PeakValley lst := by
        use x;
        -- For the StrictDecFrom part, we need to show that for all i ≥ x, if i + 1 is less than the length of the list, then lst[i]! > lst[i + 1]!.
        have h_dec : ∀ i, x ≤ i → i + 1 < lst.length → lst[i]! > lst[i + 1]! := by
          intro i hi₁ hi₂; specialize hx_dec ( i - x ) ( by omega ) ; simp_all +decide [ add_assoc, Nat.sub_add_cancel hi₁ ] ;
        exact ⟨ hx_ge, by omega, fun i hi hi' => by simpa [ List.getElem?_eq_getElem hi', List.getElem?_eq_getElem ( by omega : i + 1 < lst.length ) ] using hx_inc i hi, fun i hi hi' => by simpa [ List.getElem?_eq_getElem hi' ] using h_dec i hi hi' ⟩;
      exact h.mpr h_peak;
    · contrapose! h;
      -- By definition of PeakValley, if there's no peak, then the list isn't a peak-valley.
      have h_not_peak : ¬LLMSpec.PeakValley lst := by
        rintro ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩;
        obtain ⟨ x, hx₁, hx₂ ⟩ := h.1 p ( by linarith ) hp₁ ( by omega ) ( fun i hi => by simpa using hp₃ i hi ( by omega ) );
        exact hx₂.not_lt ( by simpa using hp₄ ( p + x ) ( by linarith ) ( by omega ) );
      grind +ring

end Proof