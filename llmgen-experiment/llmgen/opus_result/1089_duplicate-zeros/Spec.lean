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
    1089. Duplicate Zeros: duplicate each occurrence of 0 in a fixed-length integer array, shifting right and truncating.
    Natural language breakdown:
    1. Input is an array of integers with a fixed length n.
    2. We define a conceptual output stream obtained by scanning the input left-to-right.
    3. Each nonzero input element contributes exactly one output element equal to itself.
    4. Each zero input element contributes exactly two consecutive output elements, both equal to 0.
    5. The actual returned array is the first n elements of this conceptual output stream (truncate to length n).
    6. Because the original problem updates in-place and returns nothing, we model the modified array as a returned array.
    7. Therefore the result must have the same size as the input.
    8. Every output index j (0 ≤ j < n) is produced by a unique input index i, determined by how many output elements are produced by prefixes of the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: producedLen arr k = number of conceptual output elements produced by the first k input elements.
-- Each nonzero produces 1; each zero produces 2.
-- We use foldl over a prefix (arr.take k) to avoid recursion.
-- Note: we use Int = 0 propositionally; this is fine (not Float).
def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

-- Precondition: none.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the length-preserving truncation of duplicating zeros.
-- We characterize the mapping index-wise using the prefix produced lengths.
-- For each output index j, there is a unique input index i < n such that
-- producedLen arr i ≤ j < producedLen arr (i+1). The output value equals arr[i], but if arr[i]=0 then it is 0.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))
end Specs

section Impl
-- We model the in-place update as returning the updated array.
method DuplicateZeros (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  pure arr  -- placeholder

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,0,2,3,0,4,5,0]
-- Output: [1,0,0,2,3,0,0,4]
def test1_arr : Array Int := #[1, 0, 2, 3, 0, 4, 5, 0]
def test1_Expected : Array Int := #[1, 0, 0, 2, 3, 0, 0, 4]

-- Test case 2: Example 2 (no zeros)
def test2_arr : Array Int := #[1, 2, 3]
def test2_Expected : Array Int := #[1, 2, 3]

-- Test case 3: empty array
def test3_arr : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: single element zero
def test4_arr : Array Int := #[0]
def test4_Expected : Array Int := #[0]

-- Test case 5: single element nonzero
def test5_arr : Array Int := #[7]
def test5_Expected : Array Int := #[7]

-- Test case 6: all zeros (truncation preserves all zeros)
def test6_arr : Array Int := #[0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: zeros causing truncation of later elements
-- [1,0,0,2] -> conceptual: 1,0,0,0,0,2 -> take 4 => [1,0,0,0]
def test7_arr : Array Int := #[1, 0, 0, 2]
def test7_Expected : Array Int := #[1, 0, 0, 0]

-- Test case 8: negative values with zeros
-- [0,-1,0,2] -> conceptual: 0,0,-1,0,0,2 -> take 4 => [0,0,-1,0]
def test8_arr : Array Int := #[0, -1, 0, 2]
def test8_Expected : Array Int := #[0, 0, -1, 0]

-- Test case 9: trailing zero does not create a visible extra element after truncation
-- [1,2,0] -> conceptual: 1,2,0,0 -> take 3 => [1,2,0]
def test9_arr : Array Int := #[1, 2, 0]
def test9_Expected : Array Int := #[1, 2, 0]

-- Recommend to validate: boundary sizes (0/1), multiple zeros, truncation at end
end TestCases
