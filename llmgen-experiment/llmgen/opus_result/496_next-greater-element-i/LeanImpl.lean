import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (nums1 : Array Int) (nums2 : Array Int) : Array Int :=
  -- Build a HashMap from value -> next greater element using a monotone stack
  -- Process nums2 from right to left
  let n := nums2.size
  -- Helper: process nums2 from index i down to 0, maintaining stack and map
  let rec buildMap (i : Nat) (stack : List Int) (map : Std.HashMap Int Int) : Std.HashMap Int Int :=
    match i with
    | 0 => map
    | i' + 1 =>
      let val := nums2[i']!
      -- Pop elements from stack that are <= val
      let rec popStack (s : List Int) : List Int :=
        match s with
        | [] => []
        | top :: rest => if top ≤ val then popStack rest else top :: rest
      let newStack := popStack stack
      -- The next greater element is the top of the remaining stack, or -1
      let nge := match newStack with
        | [] => (-1 : Int)
        | top :: _ => top
      let newMap := map.insert val nge
      buildMap i' (val :: newStack) newMap
  let ngeMap := buildMap n [] Std.HashMap.empty
  -- Build the result array by looking up each element of nums1
  nums1.map (fun x => match ngeMap.get? x with
    | some v => v
    | none => -1)
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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums1 test1_nums2), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums1 test2_nums2), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums1 test3_nums2), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums1 test4_nums2), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums1 test5_nums2), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums1 test6_nums2), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums1 test7_nums2), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums1 test8_nums2), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums1 test9_nums2), test9_Expected]
end Assertions

section Pbt
-- Lean wrapper for velvet_plausible_test failed to compile. Giving up on PBT.

-- method implementationPbt (nums1 : Array Int) (nums2 : Array Int)
--   return (result : Array Int)
--   require precondition nums1 nums2
--   ensures postcondition nums1 nums2 result
--   do
--   return (implementation nums1 nums2)

-- velvet_plausible_test implementationPbt (config := { maxMs := some 5000 })
end Pbt

section Proof
end Proof
