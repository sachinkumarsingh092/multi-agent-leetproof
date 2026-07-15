import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (nums : Array Int) : Int :=
  -- Boyer–Moore majority vote algorithm (single pass, O(1) extra space)
  let step : (Option Int × Int) → Int → (Option Int × Int) :=
    fun state x =>
      match state with
      | (none, _) => (some x, 1)
      | (some cand, cnt) =>
          if cnt == 0 then
            (some x, 1)
          else if x == cand then
            (some cand, cnt + 1)
          else
            (some cand, cnt - 1)
  let (candOpt, _) := nums.foldl step (none, 0)
  -- Under the precondition, there is a majority element, hence candidate exists.
  match candOpt with
  | some c => c
  | none => 0
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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Proof
theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
    sorry
end Proof
