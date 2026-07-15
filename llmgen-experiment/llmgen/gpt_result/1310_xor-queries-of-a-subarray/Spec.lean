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
    XorQueriesOfASubarray: answer each query with the XOR of the subarray arr[left..right].
    **Important: complexity should be O(n + q) time and O(n) space**
    Natural language breakdown:
    1. We are given an array `arr` of natural numbers.
    2. We are given an array `queries`, where each query is a pair (left, right) of indices.
    3. Each query denotes the contiguous subarray consisting of elements at indices left, left+1, ..., right.
    4. The XOR value of a query is the bitwise XOR of all elements in that subarray.
    5. We return an array `answer` with the same length as `queries`.
    6. For each query index i, answer[i] equals the XOR of arr[left_i..right_i].
    7. Each query must be in bounds: left ≤ right and right < arr.size.
-/

section Specs
-- Helper: the subarray of `arr` from indices `l` to `r` inclusive.
-- Implemented via `extract l (r+1)`, which returns the elements with indices in [l, r+1).
def subarray (arr : Array Nat) (l : Nat) (r : Nat) : Array Nat :=
  arr.extract l (r + 1)

-- Helper: XOR of all elements in an array.
def xorAll (a : Array Nat) : Nat :=
  a.foldl (fun acc x => acc ^^^ x) 0

-- Helper: XOR of arr[l..r] inclusive.
def subarrayXor (arr : Array Nat) (l : Nat) (r : Nat) : Nat :=
  xorAll (subarray arr l r)

-- Preconditions: every query index pair is well-formed and in-bounds for `arr`.
def precondition (arr : Array Nat) (queries : Array (Nat × Nat)) : Prop :=
  ∀ (i : Nat), i < queries.size →
    let q := queries[i]!
    let l := q.1
    let r := q.2
    l ≤ r ∧ r < arr.size

-- Postconditions:
-- 1) output length equals number of queries
-- 2) each output element equals the XOR of the corresponding inclusive subarray

def postcondition (arr : Array Nat) (queries : Array (Nat × Nat)) (answer : Array Nat) : Prop :=
  answer.size = queries.size ∧
  ∀ (i : Nat), i < queries.size →
    let q := queries[i]!
    let l := q.1
    let r := q.2
    answer[i]! = subarrayXor arr l r
end Specs

section Impl
method XorQueriesOfASubarray (arr : Array Nat) (queries : Array (Nat × Nat))
  return (answer : Array Nat)
  require precondition arr queries
  ensures postcondition arr queries answer
  do
  pure #[]  -- placeholder body

end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [1,3,4,8], queries = [(0,1),(1,2),(0,3),(3,3)] => [2,7,14,8]
def test1_arr : Array Nat := #[1, 3, 4, 8]
def test1_queries : Array (Nat × Nat) := #[(0, 1), (1, 2), (0, 3), (3, 3)]
def test1_Expected : Array Nat := #[2, 7, 14, 8]

-- Test case 2: Example 2
-- arr = [4,8,2,10], queries = [(2,3),(1,3),(0,0),(0,3)] => [8,0,4,4]
def test2_arr : Array Nat := #[4, 8, 2, 10]
def test2_queries : Array (Nat × Nat) := #[(2, 3), (1, 3), (0, 0), (0, 3)]
def test2_Expected : Array Nat := #[8, 0, 4, 4]

-- Test case 3: Empty arr and no queries (degenerate valid case)
def test3_arr : Array Nat := #[]
def test3_queries : Array (Nat × Nat) := #[]
def test3_Expected : Array Nat := #[]

-- Test case 4: Singleton array with repeated identical queries
-- XOR of a single element range is the element itself

def test4_arr : Array Nat := #[13]
def test4_queries : Array (Nat × Nat) := #[(0, 0), (0, 0), (0, 0)]
def test4_Expected : Array Nat := #[13, 13, 13]

-- Test case 5: Two elements, cover each element and the full range

def test5_arr : Array Nat := #[5, 5]
def test5_queries : Array (Nat × Nat) := #[(0, 0), (1, 1), (0, 1)]
def test5_Expected : Array Nat := #[5, 5, 0]

-- Test case 6: Array with zeros and multiple ranges

def test6_arr : Array Nat := #[0, 1, 0, 1]
def test6_queries : Array (Nat × Nat) := #[(0, 3), (0, 0), (1, 2), (2, 3)]
def test6_Expected : Array Nat := #[0, 0, 1, 1]

-- Test case 7: Larger range queries stressing boundaries

def test7_arr : Array Nat := #[1, 2, 3, 4, 5]
def test7_queries : Array (Nat × Nat) := #[(0, 4), (0, 1), (3, 4), (2, 2)]
def test7_Expected : Array Nat := #[1, 3, 1, 3]

-- Test case 8: Many queries, including last index only and full range

def test8_arr : Array Nat := #[7, 6, 5, 4, 3, 2, 1]
def test8_queries : Array (Nat × Nat) := #[(6, 6), (0, 6), (1, 5), (2, 4)]
def test8_Expected : Array Nat := #[1, 0, 6, 2]
end TestCases
