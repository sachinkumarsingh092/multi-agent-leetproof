import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    RemoveDuplicatesFromSortedArrayII: given a sorted (non-decreasing) integer array, keep each value at most twice.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array of integers sorted in non-decreasing order.
    2. The output consists of a number k and an array out representing the modified array state.
    3. Only the first k elements of out are relevant; elements beyond index k are unconstrained.
    4. The first k elements must be in non-decreasing order.
    5. For every integer value x, the number of occurrences of x in the first k elements is the minimum of:
       a. 2, and
       b. the number of occurrences of x in the entire input array.
    6. Therefore, each distinct value appears at most twice in the kept prefix.
    7. Because the input is sorted and the output prefix is required to be sorted with these exact capped counts,
       the kept prefix is uniquely determined and preserves the relative order implied by sortedness.
-/

section Specs
-- Helper: count occurrences of x in the first k positions of arr.
-- Uses Array.take to avoid any out-of-bounds access.
-- Note: This is a declarative observation function used in the specification.
def countInPrefix (arr : Array Int) (k : Nat) (x : Int) : Nat :=
  (arr.take k).count x

-- Helper: non-decreasing sortedness of the first k elements.
def sortedPrefix (arr : Array Int) (k : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < k → arr[i]! ≤ arr[i + 1]!

-- Precondition: the whole input array is sorted in non-decreasing order.
def precondition (nums : Array Int) : Prop :=
  sortedPrefix nums nums.size

-- Postcondition: result is (k, out), where out is the post-state array.
def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  let k : Nat := result.1
  let out : Array Int := result.2
  out.size = nums.size ∧
  k ≤ nums.size ∧
  sortedPrefix out k ∧
  (∀ (x : Int), countInPrefix out k x = Nat.min 2 (countInPrefix nums nums.size x))
end Specs

section Impl
method RemoveDuplicatesFromSortedArrayII (nums : Array Int)
  return (result : Nat × Array Int)
  require precondition nums
  ensures postcondition nums result
  do
    pure (0, nums)  -- placeholder

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,1,1,2,2,3]
-- Output: k = 5, prefix [1,1,2,2,3]
def test1_nums : Array Int := #[1, 1, 1, 2, 2, 3]
def test1_Expected : Nat × Array Int := (5, #[1, 1, 2, 2, 3, 0])

-- Test case 2: Example 2
-- Input: [0,0,1,1,1,1,2,3,3]
-- Output: k = 7, prefix [0,0,1,1,2,3,3]
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 1, 2, 3, 3]
def test2_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 3, 3, 0, 0])

-- Test case 3: Empty array (boundary)
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])

-- Test case 4: Singleton array (boundary)
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])

-- Test case 5: All elements identical, more than twice
-- Input: [2,2,2,2] -> keep only two 2s
-- Trailing elements are arbitrary; keep size unchanged.
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (2, #[2, 2, 0, 0])

-- Test case 6: Already satisfies "at most twice" everywhere
-- Input is unchanged, k = size

def test6_nums : Array Int := #[1, 1, 2, 2, 3, 3]
def test6_Expected : Nat × Array Int := (6, #[1, 1, 2, 2, 3, 3])

-- Test case 7: Includes negative values and multiple runs exceeding 2
-- Input: [-1,-1,-1,0,0,0,1] -> prefix [-1,-1,0,0,1]
def test7_nums : Array Int := #[-1, -1, -1, 0, 0, 0, 1]
def test7_Expected : Nat × Array Int := (5, #[-1, -1, 0, 0, 1, 0, 0])

-- Test case 8: No duplicates at all (k = size)
def test8_nums : Array Int := #[0, 1, 2]
def test8_Expected : Nat × Array Int := (3, #[0, 1, 2])

-- Test case 9: Multiple groups with some exceeding 2
-- Input: [0,0,0,1,1,2,2,2,2,3] -> prefix [0,0,1,1,2,2,3]
def test9_nums : Array Int := #[0, 0, 0, 1, 1, 2, 2, 2, 2, 3]
def test9_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 2, 3, 0, 0, 0])

end TestCases
