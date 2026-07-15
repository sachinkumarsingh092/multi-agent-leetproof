/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4ea8148d-6e53-49e2-b93d-78d233148666

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem precondition_equiv (nums : List Nat) : VerinaSpec.solution_precond nums ↔ LLMSpec.precondition nums

- theorem postcondition_equiv (nums : List Nat) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.solution_postcond nums result ↔ LLMSpec.postcondition nums result)
-/

import Mathlib.Tactic

import Std.Data.HashSet


namespace VerinaSpec

open Std

def solution_precond (nums : List Nat) : Prop :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)

def solution_postcond (nums : List Nat) (result: Nat) : Prop :=
  let n := nums.length;
  let getSubarray_local := fun (i j : Nat) =>
    (nums.drop i).take (j - i + 1);
  let distinctCount_local := fun (l : List Nat) =>
    let foldFn := fun (seen : List Nat) (x : Nat) =>
      if seen.elem x then seen else x :: seen;
    let distinctElems := l.foldl foldFn [];
    distinctElems.length;
  let square_local := fun (n : Nat) => n * n;
  (1 <= n ∧ n <= 100 ∧ nums.all (fun x => 1 <= x ∧ x <= 100)) ->
  (
    result >= 0
    ∧
    let expectedSum : Nat :=
      List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
        let innerSum : Nat :=
          List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
            let j := i + d;
            let subarr := getSubarray_local i j;
            let count := distinctCount_local subarr;
            currentInnerSum + square_local count
          ) 0
        outerSum + innerSum
      ) 0;
    result = expectedSum
  )

end VerinaSpec

namespace LLMSpec

-- A contiguous slice starting at index `start` with length `len`.
-- In the postcondition we only use `start,len` pairs that keep the slice within bounds.
def sliceLen (nums : List Nat) (start : Nat) (len : Nat) : List Nat :=
  (nums.drop start).take len

-- Number of distinct elements in a list.
def distinctCount (l : List Nat) : Nat :=
  l.toFinset.card

-- Preconditions from the problem constraints.
def precondition (nums : List Nat) : Prop :=
  1 ≤ nums.length ∧
  nums.length ≤ 100 ∧
  (∀ x : Nat, x ∈ nums → 1 ≤ x ∧ x ≤ 100)

-- Postcondition: `result` is the sum over all non-empty subarrays.
-- We enumerate subarrays by choosing a start index `i` and a positive length `l+1`.
-- For each such slice, we add (distinctCount slice)^2.
-- We use `Finset.sum` explicitly to avoid parsing issues with big-operator binder notation.
def postcondition (nums : List Nat) (result : Nat) : Prop :=
  result =
    (Finset.range nums.length).sum (fun i =>
      (Finset.range (nums.length - i)).sum (fun l =>
        (distinctCount (sliceLen nums i (l + 1))) ^ 2))

end LLMSpec

section Proof

theorem precondition_equiv (nums : List Nat) : VerinaSpec.solution_precond nums ↔ LLMSpec.precondition nums := by
  -- By definition of `solution_precond` and `precondition`, we can see that they are equivalent.
  simp [VerinaSpec.solution_precond, LLMSpec.precondition]

theorem postcondition_equiv (nums : List Nat) (result : Nat) : LLMSpec.precondition nums →
  (VerinaSpec.solution_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  unfold LLMSpec.postcondition VerinaSpec.solution_postcond;
  -- By definition of `distinctCount_local`, we know that it is equivalent to `Finset.card`.
  have h_distinctCount_local_eq_finset_card : ∀ (l : List ℕ), List.length (List.foldl (fun (seen : List ℕ) (x : ℕ) => if List.elem x seen = Bool.true then seen else x :: seen) [] l) = Finset.card (List.toFinset l) := by
    intro l;
    induction' l using List.reverseRecOn with l ih;
    · rfl;
    · by_cases h : ih ∈ l <;> simp_all +decide [ Finset.card_insert_of_notMem ];
      · rw [ if_pos ];
        · assumption;
        · have h_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ∈ List.foldl (fun (seen : List ℕ) (x : ℕ) => if x ∈ seen then seen else x :: seen) [] l := by
            intros l x hx; induction' l using List.reverseRecOn with l ih <;> aesop;
          exact h_mem h;
      · split_ifs <;> simp_all +decide [ List.mem_toFinset ];
        -- By definition of `foldl`, if `ih` is in the result of folding `l`, then `ih` must be in `l`.
        have h_foldl_mem : ∀ (l : List ℕ) (ih : ℕ), ih ∈ List.foldl (fun (seen : List ℕ) (x : ℕ) => if x ∈ seen then seen else x :: seen) [] l → ih ∈ l := by
          intro l ih hi; induction' l using List.reverseRecOn with l ih <;> aesop;
        exact h ( h_foldl_mem l ih ‹_› );
  simp_all +decide [ sq, List.range_succ ];
  -- By definition of `List.foldl`, we can rewrite the left-hand side of the equation.
  have h_foldl_eq_sum : ∀ (l : List ℕ) (f : ℕ → ℕ), List.foldl (fun outerSum i => outerSum + f i) 0 l = List.sum (List.map f l) := by
    intro l f; induction' l using List.reverseRecOn with l ih <;> simp +decide [ * ] ;
  unfold LLMSpec.precondition; aesop;

end Proof