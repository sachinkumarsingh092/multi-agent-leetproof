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
    896. Monotonic Array: decide whether an integer array is monotone increasing or monotone decreasing.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. `nums` is monotone increasing if for all indices i and j with i ≤ j, we have nums[i] ≤ nums[j].
    3. `nums` is monotone decreasing if for all indices i and j with i ≤ j, we have nums[i] ≥ nums[j].
    4. The array is monotonic if it is monotone increasing or monotone decreasing.
    5. The function returns `true` exactly when the input array is monotonic, otherwise `false`.
    6. Empty arrays and single-element arrays are monotonic (both conditions hold vacuously).
-/

section Specs
-- A property-based definition of monotone increasing over Array Int using Nat indices.
-- We quantify over all i ≤ j that are valid indices.
def monotoneIncreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≤ nums[j]!

-- A property-based definition of monotone decreasing over Array Int using Nat indices.
def monotoneDecreasing (nums : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < nums.size → j < nums.size → i ≤ j → nums[i]! ≥ nums[j]!

def monotonic (nums : Array Int) : Prop :=
  monotoneIncreasing nums ∨ monotoneDecreasing nums

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ monotonic nums) ∧
  (result = false ↔ ¬ monotonic nums)
end Specs

section Impl
method MonotonicArray (nums : Array Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  pure true

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,2,2,3]
-- Output: true
def test1_nums : Array Int := #[1, 2, 2, 3]
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- Input: [6,5,4,4]
-- Output: true
def test2_nums : Array Int := #[6, 5, 4, 4]
def test2_Expected : Bool := true

-- Test case 3: Example 3
-- Input: [1,3,2]
-- Output: false
def test3_nums : Array Int := #[1, 3, 2]
def test3_Expected : Bool := false

-- Test case 4: Empty array (vacuously monotonic)
def test4_nums : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously monotonic)
def test5_nums : Array Int := #[0]
def test5_Expected : Bool := true

-- Test case 6: Constant array (both increasing and decreasing)
def test6_nums : Array Int := #[2, 2, 2, 2]
def test6_Expected : Bool := true

-- Test case 7: Strictly increasing with negatives and positives (covers -1,0,1)
def test7_nums : Array Int := #[-1, 0, 1]
def test7_Expected : Bool := true

-- Test case 8: Strictly decreasing with negatives and positives (covers 1,0,-1)
def test8_nums : Array Int := #[1, 0, -1]
def test8_Expected : Bool := true

-- Test case 9: Not monotonic due to a rise then fall
def test9_nums : Array Int := #[1, 2, 1, 2]
def test9_Expected : Bool := false
end TestCases
