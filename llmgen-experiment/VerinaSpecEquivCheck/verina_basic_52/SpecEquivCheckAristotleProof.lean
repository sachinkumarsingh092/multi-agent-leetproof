/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3e7f3569-5772-4ff7-abb1-020110e1dd2c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.BubbleSort_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.BubbleSort_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def BubbleSort_precond (a : Array Int) : Prop :=
  True

def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a

def BubbleSort_postcond (a : Array Int) (result: Array Int) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList

end VerinaSpec

namespace LLMSpec

-- Helper predicate: non-decreasing sortedness via index comparison.
-- We use Nat indices with explicit bounds to avoid Fin-index proof overhead.
def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper predicate: multiset preservation stated as equality of occurrence counts.
-- `countP` counts elements satisfying a Bool predicate; we use Bool equality `==`.
def sameElementCounts (a : Array Int) (b : Array Int) : Prop :=
  ∀ (v : Int), a.countP (fun x => x == v) = b.countP (fun x => x == v)

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  isSortedNonDecreasing result ∧
  sameElementCounts a result

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.BubbleSort_precond a ↔ LLMSpec.precondition a := by
  -- Since both preconditions are True, their equivalence is trivial.
  simp [VerinaSpec.BubbleSort_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.BubbleSort_postcond a result ↔ LLMSpec.postcondition a result) := by
  rintro -;
  constructor;
  · -- If the VerinaSpec postcondition holds, then the result array is sorted and a permutation of the input array. Since permutations preserve element counts, the LLMSpec postcondition follows directly.
    intro h
    obtain ⟨h_sorted, h_perm⟩ := h;
    refine' ⟨ _, _, _ ⟩;
    · exact List.Perm.length_eq ( List.isPerm_iff.mp h_perm );
    · intro i j hij hj;
      have := List.pairwise_iff_get.mp h_sorted;
      convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
      · grind;
      · grind;
    · -- Since the result list is a permutation of the original list, their counts for any element are equal.
      have h_count_eq : ∀ v, List.count v result.toList = List.count v a.toList := by
        -- Since the lists are permutations of each other, their counts for any element are equal.
        have h_count_eq : List.Perm result.toList a.toList := by
          exact?;
        exact fun v => h_count_eq.count_eq v;
      intro v; specialize h_count_eq v; simp_all +decide [ List.count ] ;
  · intro h
    obtain ⟨h_size, h_sorted, h_perm⟩ := h;
    constructor;
    · rw [ List.pairwise_iff_get ];
      -- Since the list is just the array's elements in order, and the array is sorted, the list must also be sorted.
      intros i j hij
      have h_le : result[i]! ≤ result[j]! := by
        exact h_sorted _ _ hij ( by simp );
      grind;
    · simp_all +decide [ List.isPerm_iff ];
      rw [ List.perm_iff_count ];
      intro x; specialize h_perm x; simp_all +decide [ List.count ] ;

end Proof