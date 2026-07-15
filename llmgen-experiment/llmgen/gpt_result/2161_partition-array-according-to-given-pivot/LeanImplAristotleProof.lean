/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e1b1aa9c-ca7d-43a5-990a-e67d828dfca7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0 (nums : Array ℤ) (pivot : ℤ) (h_precond : precondition nums pivot) : isThreeBlockPartition nums pivot (implementation nums pivot)
-/

import Lean

import Mathlib.Tactic


set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

set_option pp.funBinderTypes true

/- Problem Description
    2161. Partition Array According to Given Pivot: Rearrange an integer array into < pivot, = pivot, > pivot, stably.
    **Important: complexity should be O(n)** time and **O(n)** extra space.
    Natural language breakdown:
    1. We are given an input array `nums` of integers and an integer `pivot`.
    2. The output is an array `result` with the same length as `nums`.
    3. Every element of `result` that is less than `pivot` must appear before every element greater than `pivot`.
    4. Every element equal to `pivot` must appear between the less-than elements and the greater-than elements.
    5. The multiset of elements is preserved: `result` contains exactly the same elements with the same multiplicities as `nums`.
-/

-- Helper functions for group sizes

def countLt (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => x < pivot)

def countEq (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => x = pivot)

def countGt (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => pivot < x)

-- Helper predicate: result is partitioned into three consecutive blocks: < pivot, = pivot, > pivot.
-- The block boundaries are defined by the counts in the input.

def isThreeBlockPartition (nums : Array Int) (pivot : Int) (result : Array Int) : Prop :=
  let cL : Nat := countLt nums pivot
  let cE : Nat := countEq nums pivot
  result.size = nums.size ∧
  (∀ (i : Nat), i < result.size →
      (i < cL → result[i]! < pivot) ∧
      ((cL ≤ i ∧ i < cL + cE) → result[i]! = pivot) ∧
      (cL + cE ≤ i → pivot < result[i]!))

-- Helper predicate: element multiplicities are preserved.
-- We express this via the `count` observation for every integer value.

def sameElementCounts (nums : Array Int) (result : Array Int) : Prop :=
  ∀ (x : Int), result.count x = nums.count x

def precondition (nums : Array Int) (pivot : Int) : Prop :=
  True

def postcondition (nums : Array Int) (pivot : Int) (result : Array Int) : Prop :=
  isThreeBlockPartition nums pivot result ∧
  sameElementCounts nums result

end Specs

section Impl

def implementation (nums : Array Int) (pivot : Int) : Array Int :=
  -- Stable O(n) time, O(n) extra space: collect three groups in order, then concatenate.
  let (lt, eq, gt) :=
    nums.foldl
      (fun (acc : Array Int × Array Int × Array Int) (x : Int) =>
        let (lt, eq, gt) := acc
        if x < pivot then
          (lt.push x, eq, gt)
        else if x = pivot then
          (lt, eq.push x, gt)
        else
          (lt, eq, gt.push x))
      (#[], #[], #[])
  lt ++ eq ++ gt

end Impl

section TestCases

-- Test case 1: Example 1
def test1_nums : Array Int := #[9, 12, 5, 10, 14, 3, 10]

def test1_pivot : Int := 10

def test1_Expected : Array Int := #[9, 5, 3, 10, 10, 12, 14]

-- Test case 2: Example 2
def test2_nums : Array Int := #[-3, 4, 3, 2]

def test2_pivot : Int := 2

def test2_Expected : Array Int := #[-3, 2, 4, 3]

-- Test case 3: Empty array
def test3_nums : Array Int := #[]

def test3_pivot : Int := 0

def test3_Expected : Array Int := #[]

-- Test case 4: Single element equal to pivot
def test4_nums : Array Int := #[7]

def test4_pivot : Int := 7

def test4_Expected : Array Int := #[7]

-- Test case 5: All elements less than pivot (result should equal input)
def test5_nums : Array Int := #[-5, -2, 0, 1]

def test5_pivot : Int := 10

def test5_Expected : Array Int := #[-5, -2, 0, 1]

-- Test case 6: All elements greater than pivot (result should equal input)
def test6_nums : Array Int := #[3, 4, 5]

def test6_pivot : Int := 2

def test6_Expected : Array Int := #[3, 4, 5]

-- Test case 7: All elements equal to pivot
def test7_nums : Array Int := #[2, 2, 2, 2]

def test7_pivot : Int := 2

def test7_Expected : Array Int := #[2, 2, 2, 2]

-- Test case 8: Mixed with duplicates across groups
def test8_nums : Array Int := #[1, 4, 2, 4, 3, 2, 5]

def test8_pivot : Int := 3

def test8_Expected : Array Int := #[1, 2, 2, 3, 4, 4, 5]

-- Test case 9: Pivot appears at ends and in middle
def test9_nums : Array Int := #[5, 1, 5, 2, 5, 3]

def test9_pivot : Int := 5

def test9_Expected : Array Int := #[1, 2, 3, 5, 5, 5]

end TestCases

section Proof

theorem correctness_goal_0 (nums : Array ℤ) (pivot : ℤ) (h_precond : precondition nums pivot) : isThreeBlockPartition nums pivot (implementation nums pivot) := by
    -- By definition of `implementation`, we know that the resulting array is partitioned into three consecutive blocks: < pivot, = pivot, > pivot.
    have h_partition : ∀ (nums : Array ℤ) (pivot : ℤ), (implementation nums pivot).size = nums.size ∧ (∀ i < (implementation nums pivot).size, (i < countLt nums pivot → (implementation nums pivot)[i]! < pivot) ∧ ((countLt nums pivot ≤ i ∧ i < countLt nums pivot + countEq nums pivot) → (implementation nums pivot)[i]! = pivot) ∧ (countLt nums pivot + countEq nums pivot ≤ i → pivot < (implementation nums pivot)[i]!)) := by
      -- By definition of `implementation`, we know that the resulting array is partitioned into three consecutive blocks: < pivot, = pivot, > pivot. We can prove this by induction on the input array.
      intros nums pivot
      induction' nums using Array.recOn with nums ih;
      -- By definition of `implementation`, we can split the list into three parts: elements less than, equal to, and greater than the pivot.
      have h_split : ∀ (nums : List ℤ) (pivot : ℤ), (implementation { toList := nums } pivot) = (List.filter (fun x => x < pivot) nums).toArray ++ (List.filter (fun x => x = pivot) nums).toArray ++ (List.filter (fun x => x > pivot) nums).toArray := by
                                                                        unfold implementation;
                                                                        -- By definition of `foldl`, we can show that the accumulator is correctly updated as we process each element in the list.
                                                                        have h_foldl : ∀ (nums : List ℤ) (pivot : ℤ), (List.foldl (fun (acc : Array ℤ × Array ℤ × Array ℤ) (x : ℤ) => if x < pivot then (acc.1.push x, acc.2.1, acc.2.2) else if x = pivot then (acc.1, acc.2.1.push x, acc.2.2) else (acc.1, acc.2.1, acc.2.2.push x)) (#[], #[], #[]) nums) = ((List.filter (fun x => x < pivot) nums).toArray, (List.filter (fun x => x = pivot) nums).toArray, (List.filter (fun x => x > pivot) nums).toArray) := by
                                                                          -- We'll use induction on the list to prove that the foldl operation correctly accumulates the elements into the three arrays.
                                                                          intro nums pivot
                                                                          induction' nums using List.reverseRecOn with nums ih;
                                                                          · rfl;
                                                                          · grind +ring;
                                                                        aesop;
      unfold countLt countEq; simp +decide [ h_split ] ;
      refine' ⟨ _, _ ⟩;
      · -- By induction on the list, we can show that the sum of the lengths of the three filtered lists is equal to the length of the original list.
        induction' nums with x xs ih;
        · rfl;
        · grind;
      · grind;
    exact ⟨ h_partition nums pivot |>.1, h_partition nums pivot |>.2 ⟩

end Proof