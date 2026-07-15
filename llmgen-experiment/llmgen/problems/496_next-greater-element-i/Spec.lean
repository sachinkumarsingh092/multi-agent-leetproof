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
    496. Next Greater Element I: For each element of nums1, find its next greater element in nums2.
    **Important: complexity should be O(m + n) time and O(n) space**
    Natural language breakdown:
    1. We are given two 0-indexed arrays nums1 and nums2 of integers.
    2. All elements in each array are distinct.
    3. Every element of nums1 appears somewhere in nums2 (nums1 is a subset of nums2).
    4. For a value x located at index j in nums2, its next greater element is the first element strictly greater than x that occurs at some index k > j.
    5. If such a k exists, the answer for x is nums2[k].
    6. If no such k exists, the answer for x is -1.
    7. The returned array ans has the same length as nums1.
    8. For each i, ans[i] is determined by the position of nums1[i] within nums2 and the next-greater rule above.
-/

section Specs
-- Helper predicates are written purely in terms of Array operations (no Array/List conversion).

def DistinctArray (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i ≠ j → a[i]! ≠ a[j]!

def IsSubsetArray (small : Array Int) (big : Array Int) : Prop :=
  ∀ (i : Nat), i < small.size → ∃ (j : Nat), j < big.size ∧ big[j]! = small[i]!

-- x occurs in array a at index j.
def OccursAt (a : Array Int) (x : Int) (j : Nat) : Prop :=
  j < a.size ∧ a[j]! = x

-- k is the (index of the) next greater element for position j in a.
-- This means:
-- * it is to the right (j < k)
-- * it is strictly greater
-- * no earlier index between j and k is strictly greater (k is the first such index)
def NextGreaterIndex (a : Array Int) (j : Nat) (k : Nat) : Prop :=
  j < k ∧
  k < a.size ∧
  a[k]! > a[j]! ∧
  (∀ (t : Nat), j < t → t < k → a[t]! ≤ a[j]!)

def HasNextGreater (a : Array Int) (j : Nat) : Prop :=
  ∃ (k : Nat), NextGreaterIndex a j k

-- v is the next-greater value for index j; v = -1 iff no next-greater exists.
def NextGreaterValue (a : Array Int) (j : Nat) (v : Int) : Prop :=
  (v = (-1) ∧ ¬ HasNextGreater a j) ∨
  (∃ (k : Nat), NextGreaterIndex a j k ∧ v = a[k]!)

-- Preconditions

def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  DistinctArray nums1 ∧
  DistinctArray nums2 ∧
  IsSubsetArray nums1 nums2

-- Postconditions

def postcondition (nums1 : Array Int) (nums2 : Array Int) (ans : Array Int) : Prop :=
  ans.size = nums1.size ∧
  (∀ (i : Nat), i < nums1.size →
    ∃ (j : Nat), OccursAt nums2 nums1[i]! j ∧ NextGreaterValue nums2 j ans[i]!)
end Specs

section Impl
method NextGreaterElementI (nums1 : Array Int) (nums2 : Array Int)
  return (ans : Array Int)
  require precondition nums1 nums2
  ensures postcondition nums1 nums2 ans
  do
  pure (#[] : Array Int)  -- placeholder

end Impl

section TestCases
-- Test case 1: Example 1
-- nums1 = [4,1,2], nums2 = [1,3,4,2] => [-1,3,-1]
def test1_nums1 : Array Int := #[4, 1, 2]
def test1_nums2 : Array Int := #[1, 3, 4, 2]
def test1_Expected : Array Int := #[-1, 3, -1]

-- Test case 2: Example 2
-- nums1 = [2,4], nums2 = [1,2,3,4] => [3,-1]
def test2_nums1 : Array Int := #[2, 4]
def test2_nums2 : Array Int := #[1, 2, 3, 4]
def test2_Expected : Array Int := #[3, -1]

-- Test case 3: nums1 empty (vacuous subset), nums2 non-empty
-- ans should be empty
def test3_nums1 : Array Int := #[]
def test3_nums2 : Array Int := #[5, 1, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: both arrays empty
def test4_nums1 : Array Int := #[]
def test4_nums2 : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: singleton where no next greater exists
def test5_nums1 : Array Int := #[10]
def test5_nums2 : Array Int := #[10]
def test5_Expected : Array Int := #[-1]

-- Test case 6: singleton where next greater exists immediately
def test6_nums1 : Array Int := #[1]
def test6_nums2 : Array Int := #[1, 2]
def test6_Expected : Array Int := #[2]

-- Test case 7: includes negative values
-- nums2 = [-2, -1, -3, 0], next greater of -2 is -1, of -3 is 0
def test7_nums1 : Array Int := #[-2, -3]
def test7_nums2 : Array Int := #[-2, -1, -3, 0]
def test7_Expected : Array Int := #[-1, 0]

-- Test case 8: nums1 = nums2, mixed next-greater and -1
def test8_nums1 : Array Int := #[3, 1, 4, 2]
def test8_nums2 : Array Int := #[3, 1, 4, 2]
def test8_Expected : Array Int := #[4, 4, -1, -1]

-- Test case 9: next greater is not adjacent (must be the first greater to the right)
-- nums2 = [2,1,3]; next greater of 1 is 3
def test9_nums1 : Array Int := #[1]
def test9_nums2 : Array Int := #[2, 1, 3]
def test9_Expected : Array Int := #[3]

-- Recommend to validate: parsing, precondition satisfiable, postcondition captures “first greater to the right”
end TestCases
