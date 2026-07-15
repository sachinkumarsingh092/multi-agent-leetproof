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
    NextGreaterElement: For each value in nums1, find its next greater element as it appears in nums2.
    Natural language breakdown:
    1. We are given two 0-indexed lists of integers, nums1 and nums2.
    2. Every integer in nums1 and nums2 is unique (no duplicates).
    3. nums1 is a subset of nums2: every value that occurs in nums1 also occurs in nums2.
    4. For a value x that occurs in nums2, its next greater element is defined as the first value y
       to the right of x in nums2 such that y > x.
    5. If no such y exists to the right of x, then the next greater element of x is -1.
    6. The function returns a list of the same length as nums1.
    7. For each index i in nums1, the output at i corresponds to the next greater element of nums1[i]
       in nums2 (or -1 if none exists).
-/

section Specs
-- Helper predicate: x occurs at index i in list l.
-- We use Nat indices and `l[i]!` for safe indexing under the bound proof.
def At (l : List Int) (i : Nat) (x : Int) : Prop :=
  i < l.length ∧ l[i]! = x

-- Helper predicate: y is the next greater element of x in nums2.
-- This is defined via positions ix and iy in nums2:
--   * x is at ix, y is at iy, and ix < iy
--   * y is strictly greater than x
--   * among all elements to the right of ix that are > x, iy is the least index
--     (i.e., there is no earlier position between ix and iy with value > x).
def IsNextGreater (nums2 : List Int) (x : Int) (y : Int) : Prop :=
  ∃ (ix : Nat) (iy : Nat),
    At nums2 ix x ∧
    At nums2 iy y ∧
    ix < iy ∧
    x < y ∧
    (∀ (j : Nat), j < nums2.length → ix < j → nums2[j]! > x → iy ≤ j)

-- Helper predicate: x has no greater element to its right in nums2.
def HasNoGreaterToRight (nums2 : List Int) (x : Int) : Prop :=
  ∃ (ix : Nat),
    At nums2 ix x ∧
    (∀ (j : Nat), j < nums2.length → ix < j → nums2[j]! ≤ x)

-- Preconditions:
-- 1) nums1 and nums2 contain no duplicates
-- 2) every element of nums1 occurs in nums2

def precondition (nums1 : List Int) (nums2 : List Int) : Prop :=
  nums1.Nodup ∧
  nums2.Nodup ∧
  (∀ (x : Int), x ∈ nums1 → x ∈ nums2)

-- Postconditions:
-- 1) result has the same length as nums1
-- 2) for each i, result[i] is either -1 (and there is no greater element to the right in nums2),
--    or a value y that is the first greater element to the right.

def postcondition (nums1 : List Int) (nums2 : List Int) (result : List Int) : Prop :=
  result.length = nums1.length ∧
  (∀ (i : Nat), i < nums1.length →
    let x : Int := nums1[i]!
    (result[i]! = (-1) ∧ HasNoGreaterToRight nums2 x) ∨
    (result[i]! ≠ (-1) ∧ IsNextGreater nums2 x (result[i]!)))
end Specs

section Impl
method NextGreaterElement (nums1 : List Int) (nums2 : List Int)
  return (result : List Int)
  require precondition nums1 nums2
  ensures postcondition nums1 nums2 result
  do
  pure []

prove_correct NextGreaterElement by sorry
end Impl

section TestCases
-- Test case 1: classic example
-- nums1 = [4,1,2], nums2 = [1,3,4,2] => [-1,3,-1]
def test1_nums1 : List Int := [4, 1, 2]
def test1_nums2 : List Int := [1, 3, 4, 2]
def test1_Expected : List Int := [-1, 3, -1]

-- Test case 2: includes -1, 0, 1 and increasing suffix
-- [-1,0,1] in [-1,0,1,2] => [0,1,2]
def test2_nums1 : List Int := [-1, 0, 1]
def test2_nums2 : List Int := [-1, 0, 1, 2]
def test2_Expected : List Int := [0, 1, 2]

-- Test case 3: nums1 is empty (valid), nums2 is empty

def test3_nums1 : List Int := []
def test3_nums2 : List Int := []
def test3_Expected : List Int := []

-- Test case 4: singleton with a next greater element
-- [2] in [2,3] => [3]
def test4_nums1 : List Int := [2]
def test4_nums2 : List Int := [2, 3]
def test4_Expected : List Int := [3]

-- Test case 5: singleton with no next greater element
-- [3] in [2,3] => [-1]
def test5_nums1 : List Int := [3]
def test5_nums2 : List Int := [2, 3]
def test5_Expected : List Int := [-1]

-- Test case 6: nums1 equals nums2, strictly increasing
-- [1,2,3,4] in [1,2,3,4] => [2,3,4,-1]
def test6_nums1 : List Int := [1, 2, 3, 4]
def test6_nums2 : List Int := [1, 2, 3, 4]
def test6_Expected : List Int := [2, 3, 4, -1]

-- Test case 7: next greater skips over smaller elements
-- [1,4] in [1,3,2,4] => [3,-1]
def test7_nums1 : List Int := [1, 4]
def test7_nums2 : List Int := [1, 3, 2, 4]
def test7_Expected : List Int := [3, -1]

-- Test case 8: larger nums2 with scattered order
-- [2,5,1] in [2,1,5,3,4] => [5,-1,5]
def test8_nums1 : List Int := [2, 5, 1]
def test8_nums2 : List Int := [2, 1, 5, 3, 4]
def test8_Expected : List Int := [5, -1, 5]

-- Test case 9: decreasing nums2 gives all -1
-- [3,1] in [3,2,1,0] => [-1,-1]
def test9_nums1 : List Int := [3, 1]
def test9_nums2 : List Int := [3, 2, 1, 0]
def test9_Expected : List Int := [-1, -1]

-- Test case 10: nums1 empty but nums2 non-empty (valid edge case)
def test10_nums1 : List Int := []
def test10_nums2 : List Int := [5, 1, 7]
def test10_Expected : List Int := []

-- Recommend to validate: test1_Expected, test2_Expected, test10_Expected
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test10' (result : List Int) :
  result ≠ test10_Expected →
  ¬ postcondition test10_nums1 test10_nums2 result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test10_Expected]) (config := { numInst := 100000 })
