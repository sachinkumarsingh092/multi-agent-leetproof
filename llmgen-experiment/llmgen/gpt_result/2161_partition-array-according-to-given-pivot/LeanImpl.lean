import Lean
import Mathlib.Tactic
import Velvet.Std

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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums test1_pivot), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums test2_pivot), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums test3_pivot), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums test4_pivot), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums test5_pivot), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums test6_pivot), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums test7_pivot), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums test8_pivot), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums test9_pivot), test9_Expected]
end Assertions

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    (pivot : ℤ)
    (h_precond : precondition nums pivot)
    : isThreeBlockPartition nums pivot (implementation nums pivot) := by
    sorry

theorem correctness_goal_1
    (nums : Array ℤ)
    (pivot : ℤ)
    : sameElementCounts nums (implementation nums pivot) := by
  classical
  unfold sameElementCounts
  intro x

  set acc : Array Int × Array Int × Array Int :=
    nums.foldl
      (fun (acc : Array Int × Array Int × Array Int) (y : Int) =>
        let (lt, eq, gt) := acc
        if y < pivot then
          (lt.push y, eq, gt)
        else if y = pivot then
          (lt, eq.push y, gt)
        else
          (lt, eq, gt.push y))
      (#[], #[], #[])
    with hacc

  let motive : Nat → (Array Int × Array Int × Array Int) → Prop :=
    fun i b =>
      let (lt, eq, gt) := b
      lt.count x + eq.count x + gt.count x = (nums.extract 0 i).count x

  have hmot : motive nums.size acc := by
    have hmot' :
        motive nums.size
          (nums.foldl
            (fun (acc : Array Int × Array Int × Array Int) (y : Int) =>
              let (lt, eq, gt) := acc
              if y < pivot then
                (lt.push y, eq, gt)
              else if y = pivot then
                (lt, eq.push y, gt)
              else
                (lt, eq, gt.push y))
            (#[], #[], #[])) := by
      refine Array.foldl_induction  (motive := motive)
        (init := (#[], #[], #[]))
        (f :=
          (fun (acc : Array Int × Array Int × Array Int) (y : Int) =>
            let (lt, eq, gt) := acc
            if y < pivot then
              (lt.push y, eq, gt)
            else if y = pivot then
              (lt, eq.push y, gt)
            else
              (lt, eq, gt.push y))) ?h0 ?hf
      · simp [motive]
      · intro i b hb
        rcases b with ⟨lt, eq, gt⟩
        dsimp [motive] at hb ⊢

        let y : Int := nums[i.1]
        have hy : nums[i.1] = y := rfl
        have hyFin : nums[i] = y := by
          simpa [y] using (Fin.getElem_fin (a := nums) i i.2)

        have hcountPush (xs : Array Int) : (xs.push y).count x = xs.count x + if y = x then 1 else 0 := by
          by_cases h : y = x
          · simpa [h] using (Array.count_push_self (a := x) (xs := xs))
          · have hne : y ≠ x := h
            simpa [h] using (Array.count_push_of_ne (xs := xs) (a := x) (b := y) hne)

        have hprefix : (nums.extract 0 i.1).push y = nums.extract 0 (i.1 + 1) := by
          simpa [hy] using
            (Array.push_extract_getElem (i := 0) (j := i.1) (h := i.2))

        have hcountPrefix :
            (nums.extract 0 (i.1 + 1)).count x = (nums.extract 0 i.1).count x + if y = x then 1 else 0 := by
          calc
            (nums.extract 0 (i.1 + 1)).count x
                = ((nums.extract 0 i.1).push y).count x := by
                    simpa using congrArg (fun a => a.count x) hprefix.symm
            _ = (nums.extract 0 i.1).count x + if y = x then 1 else 0 := by
                    simpa using hcountPush (nums.extract 0 i.1)

        by_cases hlt : y < pivot
        · -- lt
          simp [hyFin, hy, hlt, hcountPrefix, hcountPush]
          -- goal now has `if y = x` added to the `lt` count
          calc
            (lt.count x + if y = x then 1 else 0) + eq.count x + gt.count x
                = (lt.count x + eq.count x + gt.count x) + if y = x then 1 else 0 := by
                    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = (nums.extract 0 i.1).count x + if y = x then 1 else 0 := by
                    simpa [hb]
        · by_cases heq : y = pivot
          · -- eq
            simp [hyFin, hy, hlt, heq.symm, hcountPrefix, hcountPush]
            calc
              lt.count x + (eq.count x + if y = x then 1 else 0) + gt.count x
                  = (lt.count x + eq.count x + gt.count x) + if y = x then 1 else 0 := by
                      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              _ = (nums.extract 0 i.1).count x + if y = x then 1 else 0 := by
                      simpa [hb]
          · -- gt
            simp [hyFin, hy, hlt, heq, hcountPrefix, hcountPush]
            calc
              lt.count x + eq.count x + (gt.count x + if y = x then 1 else 0)
                  = (lt.count x + eq.count x + gt.count x) + if y = x then 1 else 0 := by
                      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              _ = (nums.extract 0 i.1).count x + if y = x then 1 else 0 := by
                      simpa [hb]

    simpa [hacc] using hmot'

  have hsum : (let (lt, eq, gt) := acc; lt.count x + eq.count x + gt.count x) = nums.count x := by
    simpa [motive, Array.extract_size] using hmot

  have himpl : implementation nums pivot = (let (lt, eq, gt) := acc; lt ++ eq ++ gt) := by
    simp [implementation, hacc.symm]

  rcases acc with ⟨lt, eq, gt⟩
  have hsum' : lt.count x + eq.count x + gt.count x = nums.count x := by
    simpa using hsum

  calc
    (implementation nums pivot).count x
        = (lt ++ eq ++ gt).count x := by
            simpa [himpl]
    _ = lt.count x + eq.count x + gt.count x := by
            simp [Array.count_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = nums.count x := hsum'

theorem correctness_goal
    (nums : Array Int)
    (pivot : Int)
    (h_precond : precondition nums pivot)
    : postcondition nums pivot (implementation nums pivot) := by
  -- precondition is trivial
  simp [postcondition]
  constructor
  · -- three-block partition
    have h_part : isThreeBlockPartition nums pivot (implementation nums pivot) := by
      expose_names; exact (correctness_goal_0 nums pivot h_precond)
    simpa using h_part
  · -- same element counts
    have h_counts : sameElementCounts nums (implementation nums pivot) := by
      expose_names; exact (correctness_goal_1 nums pivot)
    simpa using h_counts
end Proof
