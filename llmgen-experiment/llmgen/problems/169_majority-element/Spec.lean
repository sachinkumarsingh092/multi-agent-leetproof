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
    169. Majority Element: Return the array element that appears strictly more than ⌊n/2⌋ times.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array `nums` of length `n`.
    2. For a value `x`, its frequency is the number of indices whose element equals `x`.
    3. A value `x` is a majority element if its frequency is strictly greater than ⌊n/2⌋.
    4. The problem guarantees that at least one majority element exists.
    5. The output must be a value that is a majority element of `nums`.
    6. Such a majority element is unique: if any value has frequency > ⌊n/2⌋, it must equal the output.
-/

section Specs
-- Helper: the majority threshold (⌊n/2⌋).
-- Using Nat division, since Array.size and Array.count are Nat.
def majorityThreshold (n : Nat) : Nat :=
  n / 2

-- Helper predicate: `x` is a majority element of `nums`.
def isMajority (nums : Array Int) (x : Int) : Prop :=
  nums.count x > majorityThreshold nums.size

-- Preconditions
-- The problem states a majority element always exists.
def precondition (nums : Array Int) : Prop :=
  ∃ x : Int, isMajority nums x

-- Postconditions
-- The returned value is the unique majority element.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  isMajority nums result ∧
  (∀ y : Int, isMajority nums y → y = result)
end Specs

section Impl
method MajorityElement (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,2,3] -> majority is 3
-- counts: 3 appears 2 times, n=3, ⌊n/2⌋=1

def test1_nums : Array Int := #[3, 2, 3]

def test1_Expected : Int := 3

-- Test case 2: Example 2
-- Input: [2,2,1,1,1,2,2] -> majority is 2

def test2_nums : Array Int := #[2, 2, 1, 1, 1, 2, 2]

def test2_Expected : Int := 2

-- Test case 3: Single element (smallest valid n)

def test3_nums : Array Int := #[5]

def test3_Expected : Int := 5

-- Test case 4: Two elements, both same

def test4_nums : Array Int := #[7, 7]

def test4_Expected : Int := 7

-- Test case 5: Majority is 0, includes 0 boundary value

def test5_nums : Array Int := #[0, 1, 0]

def test5_Expected : Int := 0

-- Test case 6: Majority is negative number

def test6_nums : Array Int := #[-1, -1, 2]

def test6_Expected : Int := -1

-- Test case 7: Larger odd length, clear majority

def test7_nums : Array Int := #[9, 9, 9, 1, 2]

def test7_Expected : Int := 9

-- Test case 8: Larger even length, majority just above n/2
-- n=6, threshold=3, so majority count must be >=4

def test8_nums : Array Int := #[1, 2, 2, 2, 2, 3]

def test8_Expected : Int := 2

-- Test case 9: Majority appears many times, other values mixed

def test9_nums : Array Int := #[4, 4, 4, 4, 4, 2, 3, 4, 1]

def test9_Expected : Int := 4
end TestCases
