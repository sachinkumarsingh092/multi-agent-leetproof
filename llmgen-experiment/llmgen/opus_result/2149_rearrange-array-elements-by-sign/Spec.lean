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
    2149. Rearrange Array Elements by Sign: Rearrange an even-length integer array with equal numbers of positive and negative elements so that signs alternate starting with a positive, while preserving relative order within each sign.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input is a 0-indexed array of integers of even length.
    2. Every element is either strictly positive or strictly negative (no zeros).
    3. The number of positive elements equals the number of negative elements.
    4. The output is an array of the same length that is a rearrangement (permutation) of the input.
    5. The output starts with a positive element when the array is nonempty.
    6. Consecutive elements in the output have opposite signs (equivalently, indices with even parity are positive and odd parity are negative).
    7. Among all positives (respectively negatives), their relative order in the output is the same as in the input (stable with respect to sign).
-/

section Specs
-- Helper predicates as Bool for use with Array.filter/countP.
def isPosB (x : Int) : Bool := decide (x > 0)
def isNegB (x : Int) : Bool := decide (x < 0)

def countPos (nums : Array Int) : Nat := nums.countP isPosB

def countNeg (nums : Array Int) : Nat := nums.countP isNegB

def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

-- Parity-based sign pattern for the desired result.
def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

-- Stable order within sign can be characterized by equality of the sign-filtered subsequences.
def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

-- Preconditions: even length, no zeros, equal number of positives and negatives.
def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

-- Postconditions: permutation, correct alternating sign pattern, starts with positive if nonempty,
-- and stability of relative order within each sign.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result
end Specs

section Impl
method RearrangeArrayElementsBySign (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Placeholder body only (specification-focused file)
  pure nums

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,1,-2,-5,2,-4]
-- Output: [3,-2,1,-5,2,-4]
def test1_nums : Array Int := #[3, 1, -2, -5, 2, -4]
def test1_Expected : Array Int := #[3, -2, 1, -5, 2, -4]

-- Test case 2: Example 2 (starts with a negative in input)
def test2_nums : Array Int := #[-1, 1]
def test2_Expected : Array Int := #[1, -1]

-- Test case 3: Empty array (degenerate but satisfies even length and equal counts)
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Smallest nontrivial already-correct alternating order
def test4_nums : Array Int := #[1, -1]
def test4_Expected : Array Int := #[1, -1]

-- Test case 5: Larger array where positives/negatives are grouped
-- Positives: [1,2,3], Negatives: [-1,-2,-3]
def test5_nums : Array Int := #[1, 2, 3, -1, -2, -3]
def test5_Expected : Array Int := #[1, -1, 2, -2, 3, -3]

-- Test case 6: Alternating input but begins with negative; must start with positive in output
-- Positives: [5,6], Negatives: [-5,-6]
def test6_nums : Array Int := #[-5, 5, -6, 6]
def test6_Expected : Array Int := #[5, -5, 6, -6]

-- Test case 7: Mixed order; checks stability within each sign
-- Positives in input: [2,4,6,8], Negatives: [-1,-3,-5,-7]
def test7_nums : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]
def test7_Expected : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]

-- Test case 8: All positives first but with different magnitudes; confirms stable order
-- Positives: [10,1,7], Negatives: [-2,-9,-3]
def test8_nums : Array Int := #[10, 1, 7, -2, -9, -3]
def test8_Expected : Array Int := #[10, -2, 1, -9, 7, -3]
end TestCases
