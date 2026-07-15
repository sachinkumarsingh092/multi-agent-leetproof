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

theorem precondition_equiv (nums : List Nat) :
  VerinaSpec.solution_precond nums ↔ LLMSpec.precondition nums := by
  sorry

theorem postcondition_equiv (nums : List Nat) (result: Nat) :
  LLMSpec.precondition nums →
  (VerinaSpec.solution_postcond nums result ↔ LLMSpec.postcondition nums result) := by
  sorry

end Proof
