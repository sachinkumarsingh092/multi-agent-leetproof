/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 91a2480f-f99d-44d3-ae7d-79b5e98c01fb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Int) : VerinaSpec.semiOrderedPermutation_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.semiOrderedPermutation_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  let n := nums.length
  n > 0 ∧
  List.Nodup nums ∧
  nums.all (fun x => 1 ≤ x ∧ x ≤ Int.ofNat n)

def semiOrderedPermutation_postcond (nums : List Int) (result: Int) : Prop :=
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn

end VerinaSpec

namespace LLMSpec

-- Helper: the intended size n as an Int.
def nVal (nums : List Int) : Int :=
  Int.ofNat nums.length

-- Helper: index of a value, using boolean equality.
-- For valid inputs (permutation of 1..n), the searched elements are present.
def indexOfInt (a : Int) (nums : List Int) : Nat :=
  nums.findIdx (fun x => x == a)

-- Helper: range constraint for permutation elements: every element is in [1..n].
def elemsInRange (nums : List Int) : Prop :=
  ∀ (i : Nat), i < nums.length →
    (1 ≤ nums[i]!) ∧ (nums[i]! ≤ nVal nums)

-- Helper: the swap-count formula (as Nat).
def swapCountNat (nums : List Int) : Nat :=
  let pos1 : Nat := indexOfInt 1 nums
  let posN : Nat := indexOfInt (nVal nums) nums
  let cost1 : Nat := pos1
  let costN : Nat := (nums.length - 1) - posN
  let overlap : Nat := if pos1 > posN then 1 else 0
  cost1 + costN - overlap

-- Preconditions
-- We keep them mostly decidable and avoid heavy permutation machinery.
-- We assume:
-- 1) n = nums.length is at least 1
-- 2) all elements are within [1..n]
-- 3) no duplicates
-- 4) 1 and n actually occur (captured via findIdx bounds)
def precondition (nums : List Int) : Prop :=
  nums.length ≥ 1 ∧
  elemsInRange nums ∧
  nums.Nodup ∧
  indexOfInt 1 nums < nums.length ∧
  indexOfInt (nVal nums) nums < nums.length

-- Postcondition
-- The result is exactly the minimal number of adjacent swaps, characterized by the index-based formula.
-- We return it as an Int equal to the Nat formula coerced to Int.
def postcondition (nums : List Int) (result : Int) : Prop :=
  result = Int.ofNat (swapCountNat nums)

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Int) : VerinaSpec.semiOrderedPermutation_precond nums ↔ LLMSpec.precondition nums := by
  -- By definition of `precondition`, we know that if `precondition nums` holds, then `nums` is a permutation of `1..n`, has no duplicates, and `1` and `n` are present.
  apply Iff.intro;
  · -- By definition of `precondition`, we know that if `precondition nums` holds, then `nums` is a permutation of `1..n`, has no duplicates, and `1` and `n` are present. We can use these facts to show that `precondition_ver` holds.
    intro h
    obtain ⟨h_len, h_dup, h_range⟩ := h;
    refine' ⟨ h_len, _, h_dup, _, _ ⟩;
    · -- By definition of `all`, if `h_range` is true, then every element in `nums` is in the range [1, n].
      intro i hi
      have h_element : 1 ≤ nums[i]! ∧ nums[i]! ≤ Int.ofNat nums.length := by
        aesop;
      exact h_element;
    · simp_all +decide [ LLMSpec.indexOfInt ];
      have h_perm : List.toFinset nums = Finset.Icc 1 (nums.length : ℤ) := by
        exact Finset.eq_of_subset_of_card_le ( fun x hx => Finset.mem_Icc.mpr <| h_range x <| List.mem_toFinset.mp hx ) ( by rw [ List.toFinset_card_of_nodup h_dup ] ; simpa );
      replace h_perm := Finset.ext_iff.mp h_perm 1; aesop;
    · -- Since `nVal nums` is the length of the list `nums`, and `nums` is a permutation of `1..n`, `nVal nums` must be in the list.
      have h_nVal_in_list : LLMSpec.nVal nums ∈ nums := by
        have h_nVal_in_list : List.toFinset nums = Finset.Icc 1 (Int.ofNat nums.length) := by
          -- Since the list is a permutation of 1 to n, every element in the list is in the interval [1, n], and vice versa.
          have h_subset : nums.toFinset ⊆ Finset.Icc 1 (Int.ofNat nums.length) := by
            intro x hx; aesop;
          exact Finset.eq_of_subset_of_card_le h_subset ( by rw [ List.toFinset_card_of_nodup h_dup ] ; aesop );
        -- Since `Int.ofNat nums.length` is the upper bound of the interval `Finset.Icc 1 (Int.ofNat nums.length)`, it must be in the Finset.
        have h_nVal_in_finset : Int.ofNat nums.length ∈ Finset.Icc 1 (Int.ofNat nums.length) := by
          exact Finset.mem_Icc.mpr ⟨ by simpa using h_len, by simpa ⟩;
        exact List.mem_toFinset.mp ( h_nVal_in_list.symm ▸ h_nVal_in_finset );
      have h_nVal_lt_len : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → List.findIdx (fun y => y == x) l < l.length := by
        grind;
      exact h_nVal_lt_len h_nVal_in_list;
  · -- By definition of `precondition`, if `precondition nums` holds, then `nums` is a permutation of `1..n`, has no duplicates, and `1` and `n` are present.
    intro h_precondition
    obtain ⟨h_len, h_range, h_nodup, h_pos1, h_posn⟩ := h_precondition;
    refine' ⟨ h_len, h_nodup, _ ⟩;
    simp_all +decide [ LLMSpec.elemsInRange ];
    intro x hx; obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx; specialize h_range i; aesop;

theorem postcondition_equiv (nums : List Int) (result : Int) : LLMSpec.precondition nums →
  (VerinaSpec.semiOrderedPermutation_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold VerinaSpec.semiOrderedPermutation_postcond LLMSpec.postcondition LLMSpec.swapCountNat;
  intro h
  simp [LLMSpec.indexOfInt, LLMSpec.nVal] at *;
  split_ifs <;> simp_all +decide [ List.idxOf ];
  · grind;
  · rw [ Nat.sub_sub, Nat.cast_sub ] <;> try omega;
    -- Since the list has no duplicates and contains all elements from 1 to n, the index of n is n-1.
    have h_index_n : List.findIdx (fun x => x == (↑nums.length : ℤ)) nums < nums.length := by
      exact h.2.2.2.2;
    linarith

end Proof