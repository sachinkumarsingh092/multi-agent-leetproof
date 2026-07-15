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
  -- Step 1: Compute next greater element for each index in nums2 using a monotonic stack
  -- nge[j] = next greater value for nums2[j], or -1 if none exists
  let mut nge : Array Int := Array.replicate nums2.size (-1)
  -- stack stores indices into nums2 (as Int for type compatibility)
  let mut stack : Array Nat := #[]

  -- Process nums2 from left to right
  let mut idx := 0
  while idx < nums2.size
    -- idx is bounded by nums2.size
    invariant "idx_bounds" idx ≤ nums2.size
    -- nge array size is preserved
    invariant "nge_size" nge.size = nums2.size
    -- all stack elements are indices < idx (already processed)
    invariant "stack_valid" ∀ k, k < stack.size → stack[k]! < idx
    -- all stack elements are valid indices into nums2
    invariant "stack_bound" ∀ k, k < stack.size → stack[k]! < nums2.size
    -- indices not yet processed still have nge = -1 (initial value)
    invariant "nge_untouched" ∀ j, idx ≤ j → j < nums2.size → nge[j]! = -1
    -- stack indices are strictly increasing (structural monotonic stack property)
    invariant "stack_sorted" ∀ a b, a < stack.size → b < stack.size → a < b → stack[a]! < stack[b]!
    -- elements currently on the stack still have nge = -1 (awaiting next greater)
    invariant "on_stack_default" ∀ s, s < stack.size → nge[stack[s]!]! = -1
    -- processed elements with nge=-1 are either on stack or have NextGreaterValue(-1) already
    -- (handles edge case where next greater value is literally -1)
    invariant "on_stack_or_ngv" ∀ j, j < idx → nge[j]! = -1 → (∃ s, s < stack.size ∧ stack[s]! = j) ∨ NextGreaterValue nums2 j (-1)
    -- stack elements dominate all elements between them and idx (key monotonic stack property)
    invariant "stack_dominate" ∀ s, s < stack.size → ∀ t, stack[s]! < t → t < idx → nums2[t]! ≤ nums2[stack[s]!]!
    -- if nge[j] was set (≠ -1), it correctly represents the next greater value
    invariant "nge_correct" ∀ j, j < nums2.size → nge[j]! ≠ -1 → NextGreaterValue nums2 j (nge[j]!)
    decreasing nums2.size - idx
  do
    -- Pop elements from stack whose values are less than nums2[idx]
    let mut cont := true
    while cont = true ∧ stack.size > 0
      -- nge array size preserved through inner loop
      invariant "inner_nge_size" nge.size = nums2.size
      -- idx is still a valid index during inner loop
      invariant "inner_idx_bound" idx < nums2.size
      -- remaining stack elements are still < idx
      invariant "inner_stack_valid" ∀ k, k < stack.size → stack[k]! < idx
      -- remaining stack elements are valid nums2 indices
      invariant "inner_stack_bound" ∀ k, k < stack.size → stack[k]! < nums2.size
      -- unprocessed indices still have nge = -1
      invariant "inner_nge_untouched" ∀ j, idx ≤ j → j < nums2.size → nge[j]! = -1
      -- stack remains sorted after pops
      invariant "inner_stack_sorted" ∀ a b, a < stack.size → b < stack.size → a < b → stack[a]! < stack[b]!
      -- remaining stack elements still have nge = -1
      invariant "inner_on_stack_default" ∀ s, s < stack.size → nge[stack[s]!]! = -1
      -- processed-with-nge=-1 elements are on stack or have NextGreaterValue
      invariant "inner_on_stack_or_ngv" ∀ j, j < idx → nge[j]! = -1 → (∃ s, s < stack.size ∧ stack[s]! = j) ∨ NextGreaterValue nums2 j (-1)
      -- domination property preserved for remaining stack
      invariant "inner_stack_dominate" ∀ s, s < stack.size → ∀ t, stack[s]! < t → t < idx → nums2[t]! ≤ nums2[stack[s]!]!
      -- correctness of already-set nge values preserved
      invariant "inner_nge_correct" ∀ j, j < nums2.size → nge[j]! ≠ -1 → NextGreaterValue nums2 j (nge[j]!)
      decreasing stack.size
    do
      let topIdx := stack[stack.size - 1]!
      if nums2[topIdx]! < nums2[idx]! then
        nge := nge.set! topIdx nums2[idx]!
        stack := stack.pop
      else
        cont := false
    stack := stack.push idx
    idx := idx + 1

  -- Step 2: For each element in nums1, find its index in nums2, then look up nge
  let mut ans : Array Int := #[]
  let mut i := 0
  while i < nums1.size
    -- i is bounded
    invariant "i_bounds" 0 ≤ i ∧ i ≤ nums1.size
    -- ans grows with i
    invariant "ans_size" ans.size = i
    -- nge size unchanged
    invariant "nge_size_final" nge.size = nums2.size
    -- after outer loop, ALL nge entries are correct NextGreaterValues
    -- (combines nge_correct for ≠-1 cases, stack_dominate for on-stack -1 cases,
    --  and on_stack_or_ngv for off-stack -1 cases)
    invariant "nge_all_correct" ∀ j, j < nums2.size → NextGreaterValue nums2 j (nge[j]!)
    -- all computed answers are correct
    invariant "ans_correct" ∀ k, k < i → ∃ j, OccursAt nums2 nums1[k]! j ∧ NextGreaterValue nums2 j ans[k]!
    decreasing nums1.size - i
  do
    let val := nums1[i]!
    -- Find index of val in nums2
    let mut j := 0
    let mut found := false
    while j < nums2.size ∧ found = false
      -- j is bounded
      invariant "j_bounds" 0 ≤ j ∧ j ≤ nums2.size
      -- if found, j points to val in nums2
      invariant "found_meaning" found = true → j < nums2.size ∧ nums2[j]! = val
      -- if not found, val not in nums2[0..j)
      invariant "not_found_meaning" found = false → ∀ k, k < j → nums2[k]! ≠ val
      -- nge properties propagated through search loop
      invariant "nge_size_inner" nge.size = nums2.size
      invariant "nge_all_correct_inner" ∀ jj, jj < nums2.size → NextGreaterValue nums2 jj (nge[jj]!)
      decreasing nums2.size - j
    do
      if nums2[j]! = val then
        found := true
      else
        j := j + 1
    -- j is the index of val in nums2
    let ngeVal := nge[j]!
    ans := ans.push ngeVal
    i := i + 1
  return ans
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

#assert_same_evaluation #[((NextGreaterElementI test1_nums1 test1_nums2).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((NextGreaterElementI test2_nums1 test2_nums2).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((NextGreaterElementI test3_nums1 test3_nums2).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((NextGreaterElementI test4_nums1 test4_nums2).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((NextGreaterElementI test5_nums1 test5_nums2).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((NextGreaterElementI test6_nums1 test6_nums2).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((NextGreaterElementI test7_nums1 test7_nums2).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((NextGreaterElementI test8_nums1 test8_nums2).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((NextGreaterElementI test9_nums1 test9_nums2).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test NextGreaterElementI (config := { maxMs := some 5000 })
end Pbt
