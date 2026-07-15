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
  pure #[]  -- placeholder

prove_correct SlidingWindowMaximum by sorry
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

set_option maxHeartbeats 500000

def uniqueness_test10' (result : Array Int) :
  result ≠ test10_Expected →
  ¬ postcondition test10_nums test10_k result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test10_Expected]) (config := { numInst := 100000 })
