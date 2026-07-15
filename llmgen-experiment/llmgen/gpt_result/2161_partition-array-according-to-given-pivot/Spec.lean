import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method PartitionArrayAccordingToPivot (nums : Array Int) (pivot : Int)
  return (result : Array Int)
  require precondition nums pivot
  ensures postcondition nums pivot result
  do
  -- placeholder implementation
  pure nums

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
