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
    TwoSumIISorted: Given a 1-indexed sorted array of integers, return the (1-indexed) positions of
    the unique pair of distinct elements whose sum equals a target.
    Natural language breakdown:
    1. Input is an array `numbers : Array Int` sorted in non-decreasing order.
    2. We are given an integer `target : Int`.
    3. There exist indices i and j with 0 ≤ i < j < numbers.size such that numbers[i] + numbers[j] = target.
    4. The problem guarantees this pair is unique (exactly one solution).
    5. Output is an array of length 2 containing the 1-based indices: [i+1, j+1].
    6. The two indices must be strictly increasing and within 1..numbers.size.
    7. We must not use the same element twice (captured by i < j).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: non-decreasing order on an Int array.
-- We use the standard relational characterization of sortedness by indices.
def isSortedNondecreasing (numbers : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!

-- Helper: a valid 0-based pair (i,j) witnessing the target sum.
def isWitnessPair (numbers : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target

-- Helper: uniqueness of the witness pair, expressed over 0-based indices.
def hasUniqueWitnessPair (numbers : Array Int) (target : Int) : Prop :=
  (∃ (i : Nat) (j : Nat), isWitnessPair numbers target i j) ∧
  (∀ (i₁ : Nat) (j₁ : Nat) (i₂ : Nat) (j₂ : Nat),
    isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)

-- Helper: output shape/validity and correspondence to a witness pair.
def outputMatchesUniquePair (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  (1 ≤ result[0]!) ∧ (result[0]! < result[1]!) ∧ (result[1]! ≤ numbers.size) ∧
  (numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target) ∧
  (∀ (i : Nat) (j : Nat), isWitnessPair numbers target i j →
    result[0]! = i + 1 ∧ result[1]! = j + 1)

-- Preconditions
-- We keep them simple and decidable-ish (arith + array bounds), and capture the problem guarantees.
def precondition (numbers : Array Int) (target : Int) : Prop :=
  numbers.size ≥ 2 ∧
  isSortedNondecreasing numbers ∧
  hasUniqueWitnessPair numbers target

-- Postconditions
-- Ensure the result is exactly the 1-based indices of the unique witness pair.
def postcondition (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  outputMatchesUniquePair numbers target result
end Specs

section Impl
method TwoSumIISorted (numbers : Array Int) (target : Int)
  return (result : Array Nat)
  require precondition numbers target
  ensures postcondition numbers target result
  do
  pure #[1, 2]

end Impl

section TestCases
-- Test case 1: Example 1
-- numbers = [2,7,11,15], target = 9 => [1,2]
def test1_numbers : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Array Nat := #[1, 2]

-- Test case 2: Example 2
-- numbers = [2,3,4], target = 6 => [1,3]
def test2_numbers : Array Int := #[2, 3, 4]
def test2_target : Int := 6
def test2_Expected : Array Nat := #[1, 3]

-- Test case 3: Example 3 (includes negative)
-- numbers = [-1,0], target = -1 => [1,2]
def test3_numbers : Array Int := #[-1, 0]
def test3_target : Int := -1
def test3_Expected : Array Nat := #[1, 2]

-- Test case 4: Contains duplicates, unique solution uses equal values
-- numbers = [1,1,3,4], target = 2 => [1,2]
def test4_numbers : Array Int := #[1, 1, 3, 4]
def test4_target : Int := 2
def test4_Expected : Array Nat := #[1, 2]

-- Test case 5: Duplicates but solution uses farthest pair
-- numbers = [0,0,3,4], target = 4 => [1,4]
def test5_numbers : Array Int := #[0, 0, 3, 4]
def test5_target : Int := 4
def test5_Expected : Array Nat := #[1, 4]

-- Test case 6: All negative, minimal size 2
-- numbers = [-5,-2], target = -7 => [1,2]
def test6_numbers : Array Int := #[-5, -2]
def test6_target : Int := -7
def test6_Expected : Array Nat := #[1, 2]

-- Test case 7: Larger array, solution in the middle
-- numbers = [-10,-3,0,5,9,12], target = 6 => [-3 + 9]
-- indices 2 and 5 (1-based)
def test7_numbers : Array Int := #[-10, -3, 0, 5, 9, 12]
def test7_target : Int := 6
def test7_Expected : Array Nat := #[2, 5]

-- Test case 8: Boundary-ish: uses first and last elements
-- numbers = [1,2,3,4,10], target = 11 => [1,5]
def test8_numbers : Array Int := #[1, 2, 3, 4, 10]
def test8_target : Int := 11
def test8_Expected : Array Nat := #[1, 5]

-- Test case 9: Includes many equal elements, unique solution still exists
-- numbers = [2,2,2,2,9], target = 11 => [1,5]
def test9_numbers : Array Int := #[2, 2, 2, 2, 9]
def test9_target : Int := 11
def test9_Expected : Array Nat := #[1, 5]
end TestCases
