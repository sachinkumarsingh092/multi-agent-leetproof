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
    162. Find Peak Element: return an index of any peak element in a 0-indexed integer array.
    **Important: complexity should be O(log n) time and O(1) space**
    Natural language breakdown:
    1. Input is a 0-indexed array `nums` of integers.
    2. An index `i` is a peak if `nums[i]` is strictly greater than its neighbors.
    3. Out-of-range neighbors are treated as negative infinity, so an endpoint only needs to be strictly greater than its single in-range neighbor.
    4. The function returns the index of any peak; if multiple peaks exist, any one is acceptable.
    5. To ensure a strict peak exists, adjacent elements are assumed to be different.
    6. The returned index must be a valid index into the array.
-/

section Specs
-- `IsPeakIndex nums i` means `i` is in range and strictly greater than each existing in-range neighbor.
-- The sentinel neighbors (-∞) are modeled by making the comparison obligations only when the neighbor exists.
def IsPeakIndex (nums : Array Int) (i : Nat) : Prop :=
  i < nums.size ∧
  (0 < i → nums[i]! > nums[i - 1]!) ∧
  (i + 1 < nums.size → nums[i]! > nums[i + 1]!)

-- Preconditions:
-- 1) array is nonempty so an index can be returned
-- 2) adjacent elements are distinct (standard problem constraint), ensuring existence of a strict peak
-- Note: we keep this decidable/first-order with bounded indexing.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∀ i : Nat, i + 1 < nums.size → nums[i]! ≠ nums[i + 1]!)

def postcondition (nums : Array Int) (result : Nat) : Prop :=
  IsPeakIndex nums result
end Specs

section Impl
method FindPeakElement (nums : Array Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  -- Binary search for a peak in O(log n) time.
  let n := nums.size
  -- From precondition, n > 0, so n-1 is safe and within Nat.
  let mut lo : Nat := 0
  let mut hi : Nat := n - 1

  while lo < hi
    -- Bounds: indices stay within [0, n-1].
    -- Init: lo=0, hi=n-1 and n>0, so hi<n.
    -- Preserved: updates maintain lo ≤ hi and keep hi < n.
    invariant "inv_bounds" (lo ≤ hi ∧ hi < n)
    -- Left boundary is on an "up-slope" from its left neighbor (or is at 0).
    -- Init: lo=0.
    -- Preserved: if we move lo to mid+1, we have nums[mid+1] > nums[mid] from the branch.
    invariant "inv_left_slope" (lo = 0 ∨ nums[lo]! > nums[lo - 1]!)
    -- Right boundary is on a "down-slope" to its right neighbor (or is at n-1).
    -- Init: hi=n-1.
    -- Preserved: if we move hi to mid, we have nums[mid] ≥ nums[mid+1]; with distinct-adjacent this implies nums[mid] > nums[mid+1].
    invariant "inv_right_slope" (hi = n - 1 ∨ nums[hi]! > nums[hi + 1]!)
    -- Termination: interval length shrinks.
    decreasing hi - lo
  do
    -- mid biased to the left, so mid < hi when lo < hi
    let mid : Nat := lo + (hi - lo) / 2
    -- Compare nums[mid] with nums[mid+1] to decide which side has a peak.
    if nums[mid]! < nums[mid + 1]! then
      lo := mid + 1
    else
      hi := mid

  return lo
end Impl

section TestCases
-- Test case 1: Example 1
-- nums = [1,2,3,1] has a peak at index 2 (value 3)
def test1_nums : Array Int := #[1, 2, 3, 1]
def test1_Expected : Nat := 2

-- Test case 2: Example 2 (one valid peak is at index 5 with value 6)
def test2_nums : Array Int := #[1, 2, 1, 3, 5, 6, 4]
def test2_Expected : Nat := 5

-- Test case 3: Single element (always a peak)
def test3_nums : Array Int := #[7]
def test3_Expected : Nat := 0

-- Test case 4: Strictly increasing (peak at last index)
def test4_nums : Array Int := #[1, 2, 3, 4]
def test4_Expected : Nat := 3

-- Test case 5: Strictly decreasing (peak at index 0)
def test5_nums : Array Int := #[4, 3, 2, 1]
def test5_Expected : Nat := 0

-- Test case 6: Two elements increasing (peak at index 1)
def test6_nums : Array Int := #[1, 2]
def test6_Expected : Nat := 1

-- Test case 7: Two elements decreasing (peak at index 0)
def test7_nums : Array Int := #[2, 1]
def test7_Expected : Nat := 0

-- Test case 8: Peak in the middle
-- [1,3,2] has a peak at index 1

def test8_nums : Array Int := #[1, 3, 2]
def test8_Expected : Nat := 1

-- Test case 9: Includes negative values; peak at index 3 (value 0)
-- [-3,-2,-4,0,-1] has peak 0 at index 3

def test9_nums : Array Int := #[-3, -2, -4, 0, -1]
def test9_Expected : Nat := 3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((FindPeakElement test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((FindPeakElement test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((FindPeakElement test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((FindPeakElement test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((FindPeakElement test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((FindPeakElement test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((FindPeakElement test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((FindPeakElement test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((FindPeakElement test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test FindPeakElement (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000


prove_correct FindPeakElement by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
end Proof
