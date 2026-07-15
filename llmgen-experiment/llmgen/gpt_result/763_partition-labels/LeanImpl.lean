import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    PartitionLabels: Partition a character sequence into as many contiguous parts as possible so that
    each character appears in at most one part; return the sizes of the parts.

    Natural language breakdown:
    1. Input is a list of characters `s`.
    2. A partition is described by a list of natural numbers `sizes` (part sizes).
    3. The parts are contiguous and cover the whole input in order; thus the sum of `sizes` equals `s.length`.
    4. Each part size must be positive (except that the empty input may have zero parts, i.e. `sizes = []`).
    5. Validity constraint: no character may appear in two different parts.
       Equivalently, for any indices i and j in range, if `s[i] = s[j]` then i and j must lie in the same part.
    6. Among all valid partitions, we want one with the maximum number of parts.
       (For this problem the maximum-parts partition is the intended greedy answer.)
    7. Edge cases: empty input yields an empty list of sizes; single character yields [1].
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

-- Helper Functions

-- Prefix sums, giving the start index of each part, starting from 0.
-- For sizes = [a,b,c], this is [0, a, a+b, a+b+c].
def partStarts (sizes : List Nat) : List Nat :=
  sizes.scanl (fun acc x => acc + x) 0

-- Total length represented by a list of part sizes.
def totalSize (sizes : List Nat) : Nat :=
  sizes.foldl (fun acc x => acc + x) 0

-- `InPart s sizes k i` means index `i` lies in the k-th part interval
-- [b[k], b[k+1]) where b = partStarts sizes.
-- We use `get?` and `isSome` to avoid proof obligations in the spec.
def InPart (sizes : List Nat) (k : Nat) (i : Nat) : Prop :=
  let b := partStarts sizes
  (b.get? k).isSome ∧
  (b.get? (k + 1)).isSome ∧
  (b.get? k).getD 0 ≤ i ∧
  i < (b.get? (k + 1)).getD 0

-- Partition validity:
-- 1) sizes cover the input length
-- 2) all parts are positive length (unless sizes = [])
-- 3) equal characters never appear in two different parts
--    (stated directly over indices, avoiding quantification over all Char values).
def isValidPartition (s : List Char) (sizes : List Nat) : Prop :=
  totalSize sizes = s.length ∧
  (∀ x : Nat, x ∈ sizes → x > 0) ∧
  (∀ (i : Nat) (j : Nat),
      i < s.length → j < s.length → s[i]! = s[j]! →
        ∃ k : Nat, InPart sizes k i ∧ InPart sizes k j)

-- Maximality: among all valid partitions, `sizes` uses the maximum number of parts.
def isMaxParts (s : List Char) (sizes : List Nat) : Prop :=
  isValidPartition s sizes ∧
  (∀ sizes2 : List Nat, isValidPartition s sizes2 → sizes2.length ≤ sizes.length)

-- Preconditions: none.
def precondition (s : List Char) : Prop :=
  True

-- Postcondition: result is a valid partition with maximum number of parts.
def postcondition (s : List Char) (result : List Nat) : Prop :=
  isMaxParts s result
end Specs

section Impl
def implementation (s : List Char) : List Nat :=
  let arr : Array Char := s.toArray
  let n : Nat := arr.size

  -- Find the last index of character `c` in `arr` by scanning backward.
  -- Returns 0 on empty input; callers only use it when `n > 0`.
  let rec lastIndexAux (c : Char) (i : Nat) : Nat :=
    match i with
    | 0 =>
        if h0 : n = 0 then
          0
        else
          let j := n - 1
          if arr[j]! = c then j else 0
    | i' + 1 =>
        let j := n - 1 - i'
        if arr[j]! = c then j else lastIndexAux c i'
  termination_by i

  let lastIndex (c : Char) : Nat :=
    if n = 0 then 0 else lastIndexAux c (n - 1)

  -- Greedy scan forming partitions.
  -- `endIdx` is the farthest last occurrence of any char seen in the current part.
  let rec scan (i endIdx start : Nat) (accRev : List Nat) : List Nat :=
    if h : i < n then
      let c := arr[i]!
      let endIdx' := Nat.max endIdx (lastIndex c)
      if i = endIdx' then
        let partLen := (i + 1) - start
        scan (i + 1) endIdx' (i + 1) (partLen :: accRev)
      else
        scan (i + 1) endIdx' start accRev
    else
      accRev.reverse
  termination_by n - i

  if n = 0 then []
  else
    -- Important: initialize `endIdx` to the last occurrence of the first character.
    let end0 := lastIndex arr[0]!
    scan 0 end0 0 []
end Impl

section TestCases
-- Test case 1: Example 1
-- s = "ababcbacadefegdehijhklij" -> [9,7,8]
def test1_s : List Char :=
  ['a','b','a','b','c','b','a','c','a','d','e','f','e','g','d','e','h','i','j','h','k','l','i','j']
def test1_Expected : List Nat := [9, 7, 8]

-- Test case 2: Example 2
-- s = "eccbbbbdec" -> [10]
def test2_s : List Char :=
  ['e','c','c','b','b','b','b','d','e','c']
def test2_Expected : List Nat := [10]

-- Test case 3: empty input
-- valid partition is empty list of sizes
def test3_s : List Char := []
def test3_Expected : List Nat := []

-- Test case 4: singleton
-- single part of size 1
def test4_s : List Char := ['x']
def test4_Expected : List Nat := [1]

-- Test case 5: all distinct characters => every character can be its own part
-- "abcd" -> [1,1,1,1]
def test5_s : List Char := ['a','b','c','d']
def test5_Expected : List Nat := [1,1,1,1]

-- Test case 6: all same character => must be one part
-- "zzzz" -> [4]
def test6_s : List Char := ['z','z','z','z']
def test6_Expected : List Nat := [4]

-- Test case 7: overlapping occurrences force merge
-- "abac" : 'a' spans indices 0..2 so first part length 3, then 'c'
def test7_s : List Char := ['a','b','a','c']
def test7_Expected : List Nat := [3,1]

-- Test case 8: already separable blocks
-- "aabbcc" => [2,2,2]
def test8_s : List Char := ['a','a','b','b','c','c']
def test8_Expected : List Nat := [2,2,2]

-- Test case 9: alternating two letters => must be one part
-- "abab" -> [4]
def test9_s : List Char := ['a','b','a','b']
def test9_Expected : List Nat := [4]

-- Recommend to validate: test1_s, test3_s, test6_s
end TestCases

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_s), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_s), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_s), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_s), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_s), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_s), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_s), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_s), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_s), test9_Expected]
end Assertions
