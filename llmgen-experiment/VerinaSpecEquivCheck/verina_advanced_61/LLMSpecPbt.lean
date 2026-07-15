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
    ProductExceptSelf: For each index i, compute the product of all input elements except the one at i.
    **Important: complexity should be O(n)**
    Natural language breakdown:
    1. The input is a list of integers `nums`.
    2. The output is a list of integers `result` with the same length as `nums`.
    3. For every valid index i, `result[i]` equals the product of all elements of `nums` except `nums[i]`.
    4. If i = 0, the excluded product is the product of the suffix after index 0.
    5. If i = nums.length - 1, the excluded product is the product of the prefix before the last index.
    6. For a singleton list, each output element is the empty-product, which is 1.
    7. For an empty list, the output is empty.
    8. The intended algorithm should not use division and should run in linear time, but the specification only describes the input-output relation.
-/

section Specs
-- Helper: product of a list of Int, with empty product = 1.
-- We use foldl to define the mathematical product.
def listProd (xs : List Int) : Int :=
  xs.foldl (fun acc x => acc * x) 1

-- No additional input restrictions are required for mathematical correctness in Int.
-- (The problem statement mentions 32-bit bounds, but Int is unbounded in Lean.)
def precondition (nums : List Int) : Prop :=
  True

-- The result has the same length, and each element is the product of all elements except itself.
-- This is specified via prefix/suffix products using take/drop.
def postcondition (nums : List Int) (result : List Int) : Prop :=
  result.length = nums.length ∧
  ∀ (i : Nat), i < nums.length →
    result[i]! = (listProd (nums.take i)) * (listProd (nums.drop (i + 1)))
end Specs

section Impl
method ProductExceptSelf (nums : List Int)
  return (result : List Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- placeholder implementation
  pure []

prove_correct ProductExceptSelf by sorry
end Impl

section TestCases
-- Test case 1: example from prompt
-- nums = [1,2,3,4] => [24,12,8,6]
def test1_nums : List Int := [1, 2, 3, 4]
def test1_Expected : List Int := [24, 12, 8, 6]

-- Test case 2: empty list
-- [] => []
def test2_nums : List Int := []
def test2_Expected : List Int := []

-- Test case 3: singleton list (empty-product = 1)
-- [5] => [1]
def test3_nums : List Int := [5]
def test3_Expected : List Int := [1]

-- Test case 4: contains a single zero
-- [0,1,2] => [2,0,0]
def test4_nums : List Int := [0, 1, 2]
def test4_Expected : List Int := [2, 0, 0]

-- Test case 5: contains multiple zeros
-- [0,0,3] => [0,0,0]
def test5_nums : List Int := [0, 0, 3]
def test5_Expected : List Int := [0, 0, 0]

-- Test case 6: negatives
-- [-1,2,-3] => [-6,3,-2]
def test6_nums : List Int := [-1, 2, -3]
def test6_Expected : List Int := [-6, 3, -2]

-- Test case 7: repeated values
-- [2,2,2] => [4,4,4]
def test7_nums : List Int := [2, 2, 2]
def test7_Expected : List Int := [4, 4, 4]

-- Test case 8: alternating signs
-- [1,-1,1,-1] => [1,-1,1,-1]
def test8_nums : List Int := [1, -1, 1, -1]
def test8_Expected : List Int := [1, -1, 1, -1]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : List Int) :
  result ≠ test8_Expected →
  ¬ postcondition test8_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
