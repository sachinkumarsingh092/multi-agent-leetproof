/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 294cb3cc-442b-410e-a4ee-3d941cd53785

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.CanyonSearch_precond a b ↔ LLMSpec.precondition a b

- theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Nat) : LLMSpec.precondition a b →
  (VerinaSpec.CanyonSearch_postcond a b result ↔ LLMSpec.postcondition a b result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n

def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))

end VerinaSpec

namespace LLMSpec

-- Helper: non-decreasing sortedness (allows equal neighbors)
def isSortedND (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: absolute difference as a natural number
-- `Int.natAbs` is the nonnegative absolute value of an integer, returned as `Nat`.
def absDiffNat (x : Int) (y : Int) : Nat :=
  Int.natAbs (x - y)

def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧
  b.size > 0 ∧
  isSortedND a ∧
  isSortedND b

def postcondition (a : Array Int) (b : Array Int) (result : Nat) : Prop :=
  -- Achievability: the minimum value is realized by some pair (i, j)
  (∃ (i : Nat), i < a.size ∧ ∃ (j : Nat), j < b.size ∧ result = absDiffNat a[i]! b[j]!) ∧
  -- Minimality: result is <= every pairwise absolute difference
  (∀ (i : Nat), i < a.size → ∀ (j : Nat), j < b.size → result ≤ absDiffNat a[i]! b[j]!)

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) (b : Array Int) : VerinaSpec.CanyonSearch_precond a b ↔ LLMSpec.precondition a b := by
  -- The two preconditions are equivalent because they both require the arrays to be non-empty and sorted in non-decreasing order.
  simp [VerinaSpec.CanyonSearch_precond, LLMSpec.precondition];
  -- The pairwise condition for a list is equivalent to the sortedness condition for the array.
  have h_pairwise_sorted : ∀ (arr : Array ℤ), List.Pairwise (· ≤ ·) arr.toList ↔ LLMSpec.isSortedND arr := by
    intro arr; exact ⟨fun h => by
      intro i j hij hj;
      have := List.pairwise_iff_get.mp h;
      convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
      · grind;
      · grind, fun h => by
      -- By definition of `isSortedND`, for any `i < j`, we have `arr[i]! ≤ arr[j]!`.
      have h_pairwise : ∀ i j : ℕ, i < j → j < arr.size → arr[i]! ≤ arr[j]! := by
        exact?;
      -- By definition of `List.Pairwise`, we need to show that for any `i < j`, `arr[i]! ≤ arr[j]!`.
      apply List.pairwise_iff_get.mpr;
      -- By definition of `Fin`, we can convert the indices `i` and `j` to natural numbers.
      intro i j hij
      have h_nat : i.val < j.val ∧ j.val < arr.size := by
        exact ⟨ hij, by simp ⟩;
      grind +ring⟩;
  aesop

theorem postcondition_equiv (a : Array Int) (b : Array Int) (result : Nat) : LLMSpec.precondition a b →
  (VerinaSpec.CanyonSearch_postcond a b result ↔ LLMSpec.postcondition a b result) := by
  unfold LLMSpec.precondition LLMSpec.postcondition VerinaSpec.CanyonSearch_postcond; aesop;

end Proof