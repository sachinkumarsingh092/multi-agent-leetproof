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
    TwoSumIndices: Find two indices in an integer array whose values sum to a target.
    Natural language breakdown:
    1. We are given an array `nums` of integers and an integer `target`.
    2. We must return an array `result` of exactly two natural-number indices.
    3. The indices must be valid positions in `nums`.
    4. The two indices must be different; equivalently we can require `result[0] < result[1]`.
    5. The values at those indices must add up to `target`.
    6. The output indices must be sorted in increasing order.
    7. The input is guaranteed to have exactly one solution pair of indices (with i < j).
-/

section Specs
-- A pair (i,j) is a valid two-sum witness when it is in bounds, ordered, and sums to target.
def TwoSumPair (nums : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target

-- There exists exactly one ordered pair (i<j) in bounds whose values sum to target.
def HasUniqueTwoSum (nums : Array Int) (target : Int) : Prop :=
  ∃ i j : Nat,
    TwoSumPair nums target i j ∧
    (∀ i' j' : Nat, TwoSumPair nums target i' j' → i' = i ∧ j' = j)

-- Preconditions: the input must have exactly one solution.
def precondition (nums : Array Int) (target : Int) : Prop :=
  HasUniqueTwoSum nums target

-- Postconditions: result encodes that unique solution as two sorted indices.
def postcondition (nums : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  result[0]! < result[1]! ∧
  result[1]! < nums.size ∧
  nums[result[0]!]! + nums[result[1]!]! = target ∧
  (∀ i j : Nat, TwoSumPair nums target i j → i = result[0]! ∧ j = result[1]!)
end Specs

section Impl
method TwoSumIndices (nums : Array Int) (target : Int)
  return (result : Array Nat)
  require precondition nums target
  ensures postcondition nums target result
  do
  -- Placeholder implementation only.
  pure #[0, 1]

prove_correct TwoSumIndices by sorry
end Impl

section TestCases
-- Test case 1: classic example
-- nums = [2,7,11,15], target = 9 => indices [0,1]
def test1_nums : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Array Nat := #[0, 1]

-- Test case 2: includes negatives, target 0
-- [-3,4,3,90] => -3 + 3 = 0 => [0,2]
def test2_nums : Array Int := #[-3, 4, 3, 90]
def test2_target : Int := 0
def test2_Expected : Array Nat := #[0, 2]

-- Test case 3: minimal size array (size = 2)
-- [3,3] target 6 => [0,1]
def test3_nums : Array Int := #[3, 3]
def test3_target : Int := 6
def test3_Expected : Array Nat := #[0, 1]

-- Test case 4: two zeros, target 0
-- [0,4,3,0] => 0 + 0 = 0 => [0,3]
def test4_nums : Array Int := #[0, 4, 3, 0]
def test4_target : Int := 0
def test4_Expected : Array Nat := #[0, 3]

-- Test case 5: solution at the end
-- [1,2,3,4,5] target 9 => 4 + 5 => [3,4]
def test5_nums : Array Int := #[1, 2, 3, 4, 5]
def test5_target : Int := 9
def test5_Expected : Array Nat := #[3, 4]

-- Test case 6: large magnitude integers
-- [1000000,-1000000,5] target 0 => [0,1]
def test6_nums : Array Int := #[1000000, -1000000, 5]
def test6_target : Int := 0
def test6_Expected : Array Nat := #[0, 1]

-- Test case 7: repeated value but unique index pair
-- [1,5,1] target 2 => 1 + 1 at indices (0,2)
def test7_nums : Array Int := #[1, 5, 1]
def test7_target : Int := 2
def test7_Expected : Array Nat := #[0, 2]

-- Test case 8: includes both negative and positive, target negative
-- [-10,20,1,2,3] target -8 => -10 + 2 => [0,3]
def test8_nums : Array Int := #[-10, 20, 1, 2, 3]
def test8_target : Int := -8
def test8_Expected : Array Nat := #[0, 3]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Array Nat) :
  result ≠ test8_Expected →
  ¬ postcondition test8_nums test8_target result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
