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
    SlidingWindowMaximum: Given an array of integers `nums` and a window size `k`,
    return an array containing the maximum value of each sliding window of size `k`
    as it moves from left to right.
    **Important: complexity should be O(n)**

    Natural language breakdown:
    1. A sliding window of size k starts at position 0 and moves right one position at a time.
    2. The last window starts at index nums.size - k, so there are nums.size - k + 1 windows.
    3. For each window position i (0 ≤ i ≤ nums.size - k), the window covers indices
       i, i+1, ..., i+k-1 of nums.
    4. result[i] must equal the maximum of nums[i..i+k-1], i.e.:
       a. Every element nums[j] with i ≤ j < i+k satisfies nums[j] ≤ result[i] (upper bound)
       b. Some element nums[j] with i ≤ j < i+k satisfies nums[j] = result[i] (achievability)
    5. Preconditions:
       - k ≥ 1 (window size is positive)
       - k ≤ nums.size (window fits in the array)
       - nums.size ≥ 1 (array is non-empty)
    6. Example: nums = [1,3,-1,-3,5,3,6,7], k = 3 → result = [3,3,5,5,6,7]
-/

section Specs
-- Helper: result[i] is an upper bound of the window nums[i..i+k-1]
def isWindowUpperBound (nums : Array Int) (k : Nat) (i : Nat) (v : Int) : Prop :=
  ∀ j : Nat, i ≤ j → j < i + k → nums[j]! ≤ v

-- Helper: result[i] is attained by some element of the window nums[i..i+k-1]
def isWindowAchievable (nums : Array Int) (k : Nat) (i : Nat) (v : Int) : Prop :=
  ∃ j : Nat, i ≤ j ∧ j < i + k ∧ nums[j]! = v

def precondition (nums : Array Int) (k : Nat) : Prop :=
  1 ≤ k ∧ k ≤ nums.size ∧ 1 ≤ nums.size

def postcondition (nums : Array Int) (k : Nat) (result : Array Int) : Prop :=
  result.size = nums.size - k + 1 ∧
  (∀ i : Nat, i < result.size →
    isWindowUpperBound nums k i result[i]! ∧
    isWindowAchievable nums k i result[i]!)
end Specs

section Impl
method SlidingWindowMaximum (nums : Array Int) (k : Nat)
  return (result : Array Int)
  require precondition nums k
  ensures postcondition nums k result
  do
  let n := nums.size
  -- Monotonic deque of indices, stored in a fixed-size array with head/tail pointers.
  -- Slots [head, tail) hold indices of nums in decreasing order of value.
  let mut dq : Array Nat := Array.replicate n 0
  let mut head := 0
  let mut tail := 0
  let mut result : Array Int := #[]
  let mut i := 0
  while i < n
    invariant true = true
    decreasing n - i
  do
    -- Remove indices from the back whose values are ≤ nums[i] (they can never be a max again)
    while head < tail ∧ nums[dq[tail - 1]!]! ≤ nums[i]!
      invariant true = true
      decreasing tail
    do
      tail := tail - 1
    -- Push current index at the back
    dq := dq.set! tail i
    tail := tail + 1
    -- Remove the front index if it fell out of the current window ending at i
    if dq[head]! + k ≤ i then
      head := head + 1
    -- Once the first full window is formed, record the maximum (front of deque)
    if i + 1 ≥ k then
      result := result.push (nums[dq[head]!]!)
    i := i + 1
  return result
end Impl

section TestCases
-- Test case 1: example from problem statement
def test1_nums : Array Int := #[1, 3, -1, -3, 5, 3, 6, 7]
def test1_k : Nat := 3
def test1_Expected : Array Int := #[3, 3, 5, 5, 6, 7]

-- Test case 2: singleton array with k = 1 (smallest possible input)
def test2_nums : Array Int := #[1]
def test2_k : Nat := 1
def test2_Expected : Array Int := #[1]

-- Test case 3: window covers the whole array (single window)
def test3_nums : Array Int := #[4, 2, 8, 1]
def test3_k : Nat := 4
def test3_Expected : Array Int := #[8]

-- Test case 4: all elements equal
def test4_nums : Array Int := #[5, 5, 5, 5, 5]
def test4_k : Nat := 2
def test4_Expected : Array Int := #[5, 5, 5, 5]

-- Test case 5: strictly decreasing array
def test5_nums : Array Int := #[9, 7, 5, 3, 1]
def test5_k : Nat := 2
def test5_Expected : Array Int := #[9, 7, 5, 3]

-- Test case 6: strictly increasing array
def test6_nums : Array Int := #[1, 2, 3, 4, 5]
def test6_k : Nat := 3
def test6_Expected : Array Int := #[3, 4, 5]

-- Test case 7: all negative values
def test7_nums : Array Int := #[-5, -3, -1, -4, -2]
def test7_k : Nat := 2
def test7_Expected : Array Int := #[-3, -1, -1, -2]

-- Test case 8: k = 1 (result equals the input array)
def test8_nums : Array Int := #[3, 1, 4, 1, 5, 9, 2, 6]
def test8_k : Nat := 1
def test8_Expected : Array Int := #[3, 1, 4, 1, 5, 9, 2, 6]

-- Test case 9: two elements with k equal to array size, mixed signs
def test9_nums : Array Int := #[10, -5]
def test9_k : Nat := 2
def test9_Expected : Array Int := #[10]

-- Test case 10: alternating values with repeated maximum
def test10_nums : Array Int := #[1, 3, 1, 3, 1, 3]
def test10_k : Nat := 3
def test10_Expected : Array Int := #[3, 3, 3, 3]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((SlidingWindowMaximum test1_nums test1_k).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SlidingWindowMaximum test2_nums test2_k).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SlidingWindowMaximum test3_nums test3_k).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SlidingWindowMaximum test4_nums test4_k).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SlidingWindowMaximum test5_nums test5_k).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SlidingWindowMaximum test6_nums test6_k).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SlidingWindowMaximum test7_nums test7_k).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SlidingWindowMaximum test8_nums test8_k).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SlidingWindowMaximum test9_nums test9_k).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((SlidingWindowMaximum test10_nums test10_k).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test SlidingWindowMaximum (config := { maxMs := some 5000 })
end Pbt
