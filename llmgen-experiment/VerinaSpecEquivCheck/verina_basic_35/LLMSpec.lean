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
    MoveZerosToEndStable: Rearrange an array of integers by moving all zero values to the end.
    Natural language breakdown:
    1. Input is an array of integers.
    2. Output is an array of integers with the same size as the input.
    3. The output contains exactly the same number of zeros as the input.
    4. All zeros in the output appear only at the end (i.e., after all non-zero elements).
    5. The relative order of non-zero elements is preserved.
    6. There are no preconditions; the method must work for any input array.
-/

section Specs
-- Helper: count of non-zero elements.
-- We use Bool predicates for computable counting via `Array.countP`.
def nonZeroCount (arr : Array Int) : Nat :=
  arr.countP (fun x => x != 0)

-- Helper: the number of non-zero elements strictly before index `i`.
-- This is the “rank” of the element at `i` among non-zero elements.
def nzRank (arr : Array Int) (i : Nat) : Nat :=
  (arr.take i).countP (fun x => x != 0)

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  -- Size is preserved.
  result.size = arr.size ∧
  -- The number of zeros is preserved.
  result.countP (fun x => x == 0) = arr.countP (fun x => x == 0) ∧
  -- Zeros form a suffix (all indices at/after `k` are 0, and before `k` are non-zero).
  (let k := nonZeroCount arr
   (∀ i : Nat, i < k → result[i]! ≠ 0) ∧
   (∀ i : Nat, k ≤ i → i < result.size → result[i]! = 0)) ∧
  -- Stability for non-zero elements:
  -- For every non-zero element at position `j` in the input, it appears in the output at
  -- index `nzRank arr j`.
  (∀ j : Nat, j < arr.size → arr[j]! ≠ 0 →
    (let r := nzRank arr j
     r < result.size ∧ result[r]! = arr[j]!)) ∧
  -- Coverage of all non-zero output positions:
  -- Every index in the non-zero prefix corresponds to some non-zero element of the input
  -- with the same rank.
  (let k := nonZeroCount arr
   ∀ i : Nat, i < k →
     ∃ j : Nat, j < arr.size ∧ arr[j]! ≠ 0 ∧ nzRank arr j = i ∧ result[i]! = arr[j]!)
end Specs

section Impl
method MoveZerosToEndStable (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
    pure arr  -- placeholder

end Impl

section TestCases
-- Test case 1: typical mixed array
def test1_arr : Array Int := #[0, 1, 0, 3, 12]
def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: empty array
def test2_arr : Array Int := #[]
def test2_Expected : Array Int := #[]

-- Test case 3: all zeros
def test3_arr : Array Int := #[0, 0]
def test3_Expected : Array Int := #[0, 0]

-- Test case 4: no zeros
def test4_arr : Array Int := #[1, 2, 3]
def test4_Expected : Array Int := #[1, 2, 3]

-- Test case 5: singleton zero
def test5_arr : Array Int := #[0]
def test5_Expected : Array Int := #[0]

-- Test case 6: singleton non-zero (negative)
def test6_arr : Array Int := #[-5]
def test6_Expected : Array Int := #[-5]

-- Test case 7: negatives, duplicates, and zeros interleaved
def test7_arr : Array Int := #[0, -1, 0, -1, 2, 0]
def test7_Expected : Array Int := #[-1, -1, 2, 0, 0, 0]

-- Test case 8: zeros already at the end
def test8_arr : Array Int := #[4, 0, 0]
def test8_Expected : Array Int := #[4, 0, 0]

-- Test case 9: multiple equal non-zeros with an internal zero
def test9_arr : Array Int := #[2, 2, 0, 2]
def test9_Expected : Array Int := #[2, 2, 2, 0]
end TestCases
