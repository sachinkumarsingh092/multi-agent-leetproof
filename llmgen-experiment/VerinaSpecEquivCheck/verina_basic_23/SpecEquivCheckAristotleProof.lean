/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 62a1391d-a261-42eb-8902-83871bb87535

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.differenceMinMax_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.differenceMinMax_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def differenceMinMax_precond (a : Array Int) : Prop :=
  a.size > 0

def differenceMinMax_postcond (a : Array Int) (result: Int) :=
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))

end VerinaSpec

namespace LLMSpec

-- Helper predicates describing when a value occurs in an array.
def occursIn (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

-- Upper/lower bound properties over all indices of the array.
def isUpperBound (a : Array Int) (v : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≤ v

def isLowerBound (a : Array Int) (v : Int) : Prop :=
  ∀ (i : Nat), i < a.size → v ≤ a[i]!

-- Characterization of maximum/minimum values (as elements + bound properties).
def isMaxValue (a : Array Int) (v : Int) : Prop :=
  occursIn a v ∧ isUpperBound a v

def isMinValue (a : Array Int) (v : Int) : Prop :=
  occursIn a v ∧ isLowerBound a v

-- Preconditions
-- The array must be non-empty.
def precondition (a : Array Int) : Prop :=
  a.size > 0

-- Postconditions
-- The result equals (max - min) for some max and min values of the array.
def postcondition (a : Array Int) (result : Int) : Prop :=
  ∃ (maxV : Int) (minV : Int),
    isMaxValue a maxV ∧
    isMinValue a minV ∧
    result = maxV - minV

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.differenceMinMax_precond a ↔ LLMSpec.precondition a := by
  -- The preconditions are equivalent because they both require the array to be non-empty.
  simp [VerinaSpec.differenceMinMax_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Int) : LLMSpec.precondition a →
  (VerinaSpec.differenceMinMax_postcond a result ↔ LLMSpec.postcondition a result) := by
  intro ha
  unfold VerinaSpec.differenceMinMax_postcond LLMSpec.postcondition;
  -- Let's simplify the goal using the definitions of `maxV` and `minV`.
  obtain ⟨maxV, minV, hmax, hmin⟩ : ∃ maxV minV, LLMSpec.isMaxValue a maxV ∧ LLMSpec.isMinValue a minV ∧ maxV = a.foldl (fun acc x => if x > acc then x else acc) (a[0]!) ∧ minV = a.foldl (fun acc x => if x < acc then x else acc) (a[0]!) := by
    refine' ⟨ _, _, _, _, rfl, rfl ⟩;
    · constructor;
      · -- By definition of `foldl`, the result is an element of the array.
        have h_foldl_mem : ∀ (xs : List ℤ), xs ≠ [] → List.foldl (fun acc x => if x > acc then x else acc) xs.head! xs ∈ xs := by
          -- We can prove this by induction on the list.
          intro xs hxs_nonempty
          induction' xs using List.reverseRecOn with xs ih;
          · contradiction;
          · cases xs <;> aesop;
        -- Apply the hypothesis `h_foldl_mem` to the list `a.toList`.
        have h_foldl_mem_a : List.foldl (fun acc x => if x > acc then x else acc) a[0]! a.toList ∈ a.toList := by
          convert h_foldl_mem a.toList _;
          · rcases a with ⟨ ⟨ l ⟩ ⟩ <;> aesop;
          · exact?;
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h_foldl_mem_a; use i; aesop;
      · intro i hi;
        -- By definition of `foldl`, we know that every element in the array is less than or equal to the maximum value found so far.
        have h_foldl_le_max : ∀ (xs : List ℤ), (∀ x ∈ xs, x ≤ List.foldl (fun acc x => if x > acc then x else acc) (a[0]!) xs) := by
          -- We can prove this by induction on the list `xs`.
          intro xs
          induction' xs using List.reverseRecOn with xs ih;
          · aesop;
          · grind;
        cases a ; aesop;
    · constructor;
      · -- By definition of `foldl`, the result is an element of the array.
        have h_foldl_mem : ∀ (xs : List ℤ), xs ≠ [] → (List.foldl (fun acc x => if x < acc then x else acc) xs.head! xs) ∈ xs := by
          -- We can prove this by induction on the length of the list.
          intro xs hxs_nonempty
          induction' xs using List.reverseRecOn with xs ih;
          · contradiction;
          · cases xs <;> aesop;
        -- Apply the hypothesis `h_foldl_mem` to the list of elements in the array.
        have h_foldl_mem_array : (Array.foldl (fun acc x => if x < acc then x else acc) a[0]! a) ∈ a.toList := by
          convert h_foldl_mem a.toList ( by simpa using ha.ne' ) using 1;
          rcases a with ⟨ ⟨ l ⟩ ⟩ <;> aesop;
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h_foldl_mem_array; use i; aesop;
      · intro i hi;
        -- By definition of `foldl`, we know that the result is less than or equal to every element in the array.
        have h_foldl_le : ∀ (xs : List ℤ), (∀ x ∈ xs, List.foldl (fun acc x => if x < acc then x else acc) (a[0]!) xs ≤ x) := by
          -- By induction on the list, we can show that the foldl result is less than or equal to every element in the list.
          intro xs
          induction' xs using List.reverseRecOn with xs ih;
          · aesop;
          · grind;
        specialize h_foldl_le (a.toList) (a[i]!);
        aesop;
  have h_unique_max : ∀ (v : ℤ), LLMSpec.isMaxValue a v → v = maxV := by
    intros v hv; exact (by
    exact le_antisymm ( hmax.2 _ ( hv.1.choose_spec.1 ) |> le_trans ( hv.1.choose_spec.2.ge ) ) ( hv.2 _ ( hmax.1.choose_spec.1 ) |> le_trans ( hmax.1.choose_spec.2.ge ) ))
  have h_unique_min : ∀ (v : ℤ), LLMSpec.isMinValue a v → v = minV := by
    intros v hv
    obtain ⟨hv_occ, hv_lower⟩ := hv
    obtain ⟨hv_minV_occ, hv_minV_lower⟩ := hmin.left;
    obtain ⟨ i, hi, hi' ⟩ := hv_occ; obtain ⟨ j, hj, hj' ⟩ := hv_minV_occ; linarith [ hv_lower i hi, hv_minV_lower i hi, hv_lower j hj, hv_minV_lower j hj ] ;
  grind +ring

end Proof