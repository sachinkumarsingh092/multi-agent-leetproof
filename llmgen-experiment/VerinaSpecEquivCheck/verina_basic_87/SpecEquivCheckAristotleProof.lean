/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7e0d53ad-018b-4c43-9d0b-74afceeb4882

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (a : Array Int) : VerinaSpec.SelectionSort_precond a ↔ LLMSpec.precondition a

- theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.SelectionSort_postcond a result ↔ LLMSpec.postcondition a result)
-/

import Mathlib.Tactic


namespace VerinaSpec

def SelectionSort_precond (a : Array Int) : Prop :=
  True

def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

def SelectionSort_postcond (a : Array Int) (result: Array Int) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList

end VerinaSpec

namespace LLMSpec

-- Helper: non-decreasing sortedness for arrays using Nat indices.
-- Strong form: for all i < j within bounds, arr[i] ≤ arr[j].
def ArrayNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- Helper: count how many times a value occurs in an array.
-- This is a purely observational property used to express multiset equality.
def elemCount (arr : Array Int) (v : Int) : Nat :=
  arr.foldl (fun (acc : Nat) (x : Int) => if decide (x = v) then acc + 1 else acc) 0

-- Helper: two arrays contain exactly the same multiset of elements (same size and same counts).
def SameMultiset (x : Array Int) (y : Array Int) : Prop :=
  x.size = y.size ∧
  ∀ (v : Int), elemCount x v = elemCount y v

-- No preconditions: any array is a valid input to sorting.
def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ArrayNondecreasing result ∧
  SameMultiset result a

end LLMSpec

section Proof

theorem precondition_equiv (a : Array Int) : VerinaSpec.SelectionSort_precond a ↔ LLMSpec.precondition a := by
  -- Since both preconditions are True, the equivalence holds trivially.
  simp [VerinaSpec.SelectionSort_precond, LLMSpec.precondition]

theorem postcondition_equiv (a : Array Int) (result : Array Int) : LLMSpec.precondition a →
  (VerinaSpec.SelectionSort_postcond a result ↔ LLMSpec.postcondition a result) := by
  -- To prove the equivalence of the postconditions, we need to show that the result being sorted and a permutation is equivalent to being non-decreasing and a permutation.
  intro h_pre
  constructor;
  · intro h;
    obtain ⟨h_sorted, h_perm⟩ := h;
    refine' ⟨ _, _, _ ⟩;
    · -- Since the result is a permutation of the input, their sizes must be equal.
      have h_size : result.toList.length = a.toList.length := by
        exact List.Perm.length_eq ( by simpa using List.isPerm_iff.mp h_perm ) ▸ rfl;
      exact h_size;
    · intro i j hij hj;
      have := List.pairwise_iff_get.mp h_sorted;
      convert this ⟨ i, by simpa using by linarith ⟩ ⟨ j, by simpa using by linarith ⟩ hij;
      · grind;
      · grind;
    · constructor;
      · simp_all +decide [ List.isPerm_iff ];
        simpa using h_perm.length_eq.symm;
      · intro v
        have h_count : List.count v a.toList = List.count v result.toList := by
          -- Since `a.toList` and `result.toList` are permutations of each other, their counts for any element are equal.
          have h_count_eq : List.Perm a.toList result.toList := by
            exact?;
          exact h_count_eq.count_eq _;
        convert h_count.symm using 1;
        · unfold LLMSpec.elemCount;
          conv => rw [ ← Array.foldl_toList ] ;
          induction' result.toList using List.reverseRecOn with x xs ih <;> aesop;
        · unfold LLMSpec.elemCount;
          conv => rw [ ← Array.foldl_toList ] ;
          induction a.toList using List.reverseRecOn <;> aesop;
  · rintro ⟨ h₁, h₂, h₃ ⟩;
    constructor;
    · rw [ List.pairwise_iff_get ];
      -- Since the list is just the elements of the array in order, if i < j in the list, then in the array, the element at i is less than or equal to the element at j.
      intros i j hij
      have h_array : result[i]! ≤ result[j]! := by
        exact h₂ _ _ hij ( by simp );
      grind;
    · -- Since the counts of elements in result and a are equal, their lists are permutations of each other.
      have h_perm : List.Perm result.toList a.toList := by
        -- Since the counts of elements in result and a are equal, their lists are permutations of each other by definition of permutation.
        have h_perm : ∀ v : ℤ, List.count v result.toList = List.count v a.toList := by
          intro v
          have := h₃.right v
          simp [LLMSpec.elemCount] at this;
          -- By definition of `List.count`, we can rewrite the goal in terms of the foldl operation.
          have h_count_eq : ∀ (l : List ℤ), List.count v l = List.foldl (fun (acc : ℕ) (x : ℤ) => if x = v then acc + 1 else acc) 0 l := by
            intro l; induction' l using List.reverseRecOn with l ih <;> aesop;
          grind +ring;
        grind;
      exact?

end Proof