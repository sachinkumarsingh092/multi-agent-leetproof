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
    verina_advanced_52: Minimum removals from the end of a list to collect all integers 1..k.

    Natural language breakdown:
    1. We are given a list `nums` of positive natural numbers and a positive natural number `k`.
    2. One operation removes the last element of `nums` and adds it to a collection.
    3. Only collected elements with value ≤ k matter for completion.
    4. The goal is to make the collection contain every integer from 1 to k (inclusive).
    5. It is assumed that the input list contains every integer in the range 1..k at least once.
    6. The output is the minimum number of operations needed to achieve this.
-/

section Specs
-- The sublist consisting of the last `r` elements of `nums`.
-- This is exactly the multiset of elements collected after performing `r` removals from the end.
def collectedSuffix (nums : List Nat) (r : Nat) : List Nat :=
  nums.drop (nums.length - r)

-- All numbers in the range 1..k appear in the collected suffix.
def coversRange (nums : List Nat) (k : Nat) (r : Nat) : Prop :=
  ∀ (t : Nat), 1 ≤ t → t ≤ k → t ∈ collectedSuffix nums r

-- Preconditions:
-- 1) k is positive
-- 2) nums contains all integers from 1..k
-- Note: We do not require nums elements to be > 0 explicitly since Nat already enforces non-negativity,
-- and the main required domain constraint is that 1..k are present.
def precondition (nums : List Nat) (k : Nat) : Prop :=
  k > 0 ∧
  (∀ (t : Nat), 1 ≤ t → t ≤ k → t ∈ nums)

-- Postcondition:
-- result is a valid number of removals (≤ length)
-- the last `result` elements cover 1..k
-- and `result` is minimal with that property.
def postcondition (nums : List Nat) (k : Nat) (result : Nat) : Prop :=
  result ≤ nums.length ∧
  coversRange nums k result ∧
  (∀ (r' : Nat), r' < result → ¬ coversRange nums k r')
end Specs

section Impl
method MinOpsCollect1ToK (nums : List Nat) (k : Nat)
  return (result : Nat)
  require precondition nums k
  ensures postcondition nums k result
  do
  pure 0  -- placeholder body

end Impl

section TestCases
-- Test case 1: representative example
def test1_nums : List Nat := [3, 1, 2, 4]
def test1_k : Nat := 2
def test1_Expected : Nat := 3

-- Test case 2: smallest k and singleton list
def test2_nums : List Nat := [1]
def test2_k : Nat := 1
def test2_Expected : Nat := 1

-- Test case 3: k = 1, last element already is 1
def test3_nums : List Nat := [2, 1]
def test3_k : Nat := 1
def test3_Expected : Nat := 1

-- Test case 4: need to collect all elements (k equals length and exact permutation)
def test4_nums : List Nat := [1, 2, 3]
def test4_k : Nat := 3
def test4_Expected : Nat := 3

-- Test case 5: permutation where needed numbers are spread; still requires removing all
def test5_nums : List Nat := [2, 3, 1]
def test5_k : Nat := 3
def test5_Expected : Nat := 3

-- Test case 6: long prefix of irrelevant (>k) values; only last 3 matter
def test6_nums : List Nat := [5, 4, 3, 2, 1]
def test6_k : Nat := 3
def test6_Expected : Nat := 3

-- Test case 7: duplicates present; minimum is still 3 due to last occurrence positions
def test7_nums : List Nat := [1, 3, 2, 1, 2, 3]
def test7_k : Nat := 3
def test7_Expected : Nat := 3

-- Test case 8: k = 1 but 1 is at the front; must remove all elements to reach it
def test8_nums : List Nat := [1, 2, 3, 4, 5]
def test8_k : Nat := 1
def test8_Expected : Nat := 5

-- Test case 9: duplicates of required numbers; can stop early
def test9_nums : List Nat := [1, 2, 1, 2]
def test9_k : Nat := 2
def test9_Expected : Nat := 2
end TestCases
