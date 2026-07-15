/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: adab6f69-ffbf-4901-9a5f-dec5700652ef

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (lst : List Int) : VerinaSpec.findProduct_precond lst ↔ LLMSpec.precondition lst

- theorem postcondition_equiv (lst : List Int) (result : Int) : LLMSpec.precondition lst →
  (VerinaSpec.findProduct_postcond lst result ↔ LLMSpec.postcondition lst result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none

def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)

def findProduct_postcond (lst : List Int) (result: Int) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True

end VerinaSpec

namespace LLMSpec

-- Helper predicates as Bool so they can be used with List.find?
def isEvenB (n : Int) : Bool := (n % 2) == 0

def isOddB (n : Int) : Bool := (n % 2) == 1

-- The precondition requires existence of at least one even and one odd element.
-- We express this via List.find? returning some value.
def precondition (lst : List Int) : Prop :=
  (lst.find? isEvenB).isSome = true ∧
  (lst.find? isOddB).isSome = true

-- Postcondition: result equals the product of the first even and first odd elements.
-- We pin down “first” using List.find? itself (which is defined as left-to-right search).
def postcondition (lst : List Int) (result : Int) : Prop :=
  ∃ (e : Int) (o : Int),
    lst.find? isEvenB = some e ∧
    lst.find? isOddB = some o ∧
    result = e * o

end LLMSpec

section Proof

theorem precondition_equiv (lst : List Int) : VerinaSpec.findProduct_precond lst ↔ LLMSpec.precondition lst := by
  -- The length condition is implicit in the existence of both `isEven` and `isOdd` elements.
  simp [VerinaSpec.findProduct_precond, LLMSpec.precondition];
  -- The length condition is redundant given the existence of both `isEven` and `isOdd` elements.
  apply Iff.intro;
  · unfold VerinaSpec.isEven VerinaSpec.isOdd LLMSpec.isEvenB LLMSpec.isOddB; aesop;
  · -- If there's an even and an odd element in the list, then the list must have at least two elements.
    intro h
    obtain ⟨x, hx_even, y, hy_odd⟩ := h
    have h_len : 1 < lst.length := by
      rcases lst with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ LLMSpec.isEvenB, LLMSpec.isOddB ];
      simp_all +decide only [Int.dvd_iff_emod_eq_zero];
    unfold LLMSpec.isEvenB LLMSpec.isOddB at *; unfold VerinaSpec.isEven VerinaSpec.isOdd at *; aesop;

theorem postcondition_equiv (lst : List Int) (result : Int) : LLMSpec.precondition lst →
  (VerinaSpec.findProduct_postcond lst result ↔ LLMSpec.postcondition lst result) := by
  -- Since the postconditions are equivalent under the same precondition, we can conclude that the two postconditions are equivalent when the precondition holds.
  intros h_pre
  simp [VerinaSpec.findProduct_postcond, LLMSpec.postcondition, h_pre];
  -- Since the lists are non-empty and contain both even and odd elements, the findIdx? functions will return some indices.
  have h_findIdx : List.findIdx? VerinaSpec.isEven lst ≠ none ∧ List.findIdx? VerinaSpec.isOdd lst ≠ none := by
    -- Since the list contains at least one even and one odd element, the findIdx? functions will find them and return some value.
    have h_even : ∃ x ∈ lst, VerinaSpec.isEven x := by
      unfold LLMSpec.precondition at h_pre; aesop;
    have h_odd : ∃ x ∈ lst, VerinaSpec.isOdd x := by
      -- Since there's at least one odd element in the list, the findIdx? VerinaSpec.isOdd lst cannot be none.
      have h_odd : ∃ x ∈ lst, LLMSpec.isOddB x := by
        unfold LLMSpec.precondition at h_pre; aesop;
      unfold LLMSpec.isOddB VerinaSpec.isOdd at *; aesop;
    grind;
  -- Since the findIdx? functions return some values, we can extract the indices and use them to show that the postconditions are equivalent.
  obtain ⟨ei, hi_even⟩ : ∃ ei, List.findIdx? VerinaSpec.isEven lst = some ei := by
    exact Option.ne_none_iff_exists'.mp h_findIdx.1
  obtain ⟨oi, hi_odd⟩ : ∃ oi, List.findIdx? VerinaSpec.isOdd lst = some oi := by
    exact Option.ne_none_iff_exists'.mp h_findIdx.2;
  -- Since the findIdx? functions return some values, we can extract the elements from the list and use them to show that the postconditions are equivalent.
  have h_elements : List.find? LLMSpec.isEvenB lst = some (lst[ei]!) ∧ List.find? LLMSpec.isOddB lst = some (lst[oi]!) := by
    have h_elements : ∀ {p : ℤ → Bool} {l : List ℤ} {i : ℕ}, List.findIdx? p l = some i → List.find? (fun x => p x) l = some (l[i]!) := by
      -- We can prove this by induction on the list.
      intros p l i hi
      induction' l with hd tl ih generalizing i;
      · cases hi;
      · rw [ List.findIdx?_cons ] at hi ; aesop;
    convert h_elements hi_odd using 1;
    unfold VerinaSpec.isOdd LLMSpec.isOddB; aesop;
  unfold VerinaSpec.firstEvenOddIndices; aesop;

end Proof