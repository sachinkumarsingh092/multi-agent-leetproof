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
    CountUniqueSorted: Count the number of unique elements in a sorted list of integers.
    Natural language breakdown:
    1. Input is a list of integers `nums`.
    2. The input list is sorted in non-decreasing order.
    3. Two elements are considered the same if they are equal as integers.
    4. The number of unique elements is the count of distinct integer values that appear at least once in `nums`.
    5. The output `result` is a natural number.
    6. Empty input has 0 unique elements.
    7. If all elements are equal, the unique count is 1.
-/

section Specs
-- A list `u` represents the set of values appearing in `nums` when:
-- (a) `u` has no duplicates
-- (b) membership in `u` is equivalent to membership in `nums`
-- For a sorted input, such a `u` corresponds to the unique values.
def representsUniques (nums : List Int) (u : List Int) : Prop :=
  u.Nodup ∧ (∀ x : Int, x ∈ u ↔ x ∈ nums)

-- Precondition: the input list is sorted in non-decreasing order.
def precondition (nums : List Int) : Prop :=
  nums.Sorted (· ≤ ·)

-- Postcondition: the result equals the length of some duplicate-free list
-- that contains exactly the values appearing in `nums`.
-- This characterizes the number of distinct values in `nums`.
def postcondition (nums : List Int) (result : Nat) : Prop :=
  ∃ u : List Int,
    representsUniques nums u ∧
    result = u.length
end Specs

section Impl
method CountUniqueSorted (nums : List Int)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0  -- placeholder

prove_correct CountUniqueSorted by sorry
end Impl

section TestCases
-- Test case 1: typical sorted list with some duplicates
def test1_nums : List Int := [1, 1, 2, 2, 2, 3]
def test1_Expected : Nat := 3

-- Test case 2: empty list
def test2_nums : List Int := []
def test2_Expected : Nat := 0

-- Test case 3: singleton list
def test3_nums : List Int := [7]
def test3_Expected : Nat := 1

-- Test case 4: all elements identical
def test4_nums : List Int := [5, 5, 5, 5]
def test4_Expected : Nat := 1

-- Test case 5: already all unique
def test5_nums : List Int := [0, 1, 2, 3, 4]
def test5_Expected : Nat := 5

-- Test case 6: includes negative numbers and duplicates
def test6_nums : List Int := [-3, -3, -1, 0, 0, 2]
def test6_Expected : Nat := 4

-- Test case 7: boundary-like small values, duplicates around 0
def test7_nums : List Int := [0, 0, 0, 1]
def test7_Expected : Nat := 2

-- Test case 8: long run of duplicates followed by new values
def test8_nums : List Int := [1, 1, 1, 1, 2, 3, 3, 4]
def test8_Expected : Nat := 4

-- Test case 9: strictly increasing with large magnitude integers
def test9_nums : List Int := [-1000000, -2, 10, 999999]
def test9_Expected : Nat := 4
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test3' (result : Nat) :
  result ≠ test3_Expected →
  ¬ postcondition test3_nums result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test3_Expected]) (config := { numInst := 100000 })
