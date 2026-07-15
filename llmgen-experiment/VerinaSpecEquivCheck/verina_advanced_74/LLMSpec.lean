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
    verina_advanced_74: Sum over all contiguous subarrays of (number of distinct elements in the subarray)^2.
    Natural language breakdown:
    1. Input is a list of natural numbers `nums`.
    2. A subarray means a contiguous slice of `nums` determined by a start index `i` and a positive length `len`, such that the slice stays within the list.
    3. The distinct-element count of a subarray is the number of different values appearing in that slice.
    4. The value contributed by a subarray is the square of its distinct-element count.
    5. The output is the sum of these values over all possible non-empty subarrays.
    6. Constraints: 1 ≤ nums.length ≤ 100 and every element is between 1 and 100 (inclusive).
-/

section Specs
-- A contiguous slice starting at index `start` with length `len`.
-- In the postcondition we only use `start,len` pairs that keep the slice within bounds.
def sliceLen (nums : List Nat) (start : Nat) (len : Nat) : List Nat :=
  (nums.drop start).take len

-- Number of distinct elements in a list.
def distinctCount (l : List Nat) : Nat :=
  l.toFinset.card

-- Preconditions from the problem constraints.
def precondition (nums : List Nat) : Prop :=
  1 ≤ nums.length ∧
  nums.length ≤ 100 ∧
  (∀ x : Nat, x ∈ nums → 1 ≤ x ∧ x ≤ 100)

-- Postcondition: `result` is the sum over all non-empty subarrays.
-- We enumerate subarrays by choosing a start index `i` and a positive length `l+1`.
-- For each such slice, we add (distinctCount slice)^2.
-- We use `Finset.sum` explicitly to avoid parsing issues with big-operator binder notation.
def postcondition (nums : List Nat) (result : Nat) : Prop :=
  result =
    (Finset.range nums.length).sum (fun i =>
      (Finset.range (nums.length - i)).sum (fun l =>
        (distinctCount (sliceLen nums i (l + 1))) ^ 2))
end Specs

section Impl
method solution (nums : List Nat)
  return (result : Nat)
  require precondition nums
  ensures postcondition nums result
  do
    pure 0

end Impl

section TestCases
-- Test case 1: example-style small list with repetition
-- nums = [1,2,1]
-- ([1]=1, [2]=1, [1]=1, [1,2]=4, [2,1]=4, [1,2,1]=4) total = 15
def test1_nums : List Nat := [1, 2, 1]
def test1_Expected : Nat := 15

-- Test case 2: minimum length (singleton)
def test2_nums : List Nat := [5]
def test2_Expected : Nat := 1

-- Test case 3: all equal elements
-- n=3 => number of subarrays = 6, each has distinctCount=1 => sum=6
def test3_nums : List Nat := [1, 1, 1]
def test3_Expected : Nat := 6

-- Test case 4: all distinct elements
-- nums=[1,2,3], sum = 3*1 + 2*4 + 1*9 = 20
def test4_nums : List Nat := [1, 2, 3]
def test4_Expected : Nat := 20

-- Test case 5: mixed distinct growth
-- nums=[1,2,1,3], expected total=38
def test5_nums : List Nat := [1, 2, 1, 3]
def test5_Expected : Nat := 38

-- Test case 6: symmetry with duplicates
-- nums=[1,2,2,1], expected total=25
def test6_nums : List Nat := [1, 2, 2, 1]
def test6_Expected : Nat := 25

-- Test case 7: maximum length boundary (100 elements), all same
-- Every subarray has distinctCount=1 => each contributes 1.
-- Number of subarrays for n=100 is 100*101/2 = 5050.
def test7_nums : List Nat := List.replicate 100 1
def test7_Expected : Nat := 5050

-- Test case 8: boundary values in element range
-- nums=[1,100] => [1]=1,[100]=1,[1,100]=4 => sum=6
def test8_nums : List Nat := [1, 100]
def test8_Expected : Nat := 6

-- Test case 9: periodic repetition
-- nums=[1,2,3,1,2], expected total=75
def test9_nums : List Nat := [1, 2, 3, 1, 2]
def test9_Expected : Nat := 75

-- Recommend to validate: test1_Expected, test7_Expected, test9_Expected
end TestCases
