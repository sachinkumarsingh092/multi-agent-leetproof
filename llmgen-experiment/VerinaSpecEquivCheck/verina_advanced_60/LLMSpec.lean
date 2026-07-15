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
    PartitionEvenOdd: Partition a list of natural numbers into evens and odds, preserving order
    Natural language breakdown:
    1. Input is a list of natural numbers `nums`.
    2. The input list contains no duplicate elements.
    3. The output is a pair `(evens, odds)` of lists of natural numbers.
    4. `evens` contains exactly the elements of `nums` whose remainder mod 2 is 0.
    5. `odds` contains exactly the elements of `nums` whose remainder mod 2 is 1.
    6. The relative order of elements in `evens` matches their order in `nums`.
    7. The relative order of elements in `odds` matches their order in `nums`.
    8. Every element of `nums` appears in exactly one of the two output lists.
-/

section Specs
-- Helper predicates for parity, defined using modulo so they are available in this environment.
def isEven (n : Nat) : Prop := n % 2 = 0

def isOdd (n : Nat) : Prop := n % 2 = 1

def precondition (nums : List Nat) : Prop :=
  nums.Nodup

def postcondition (nums : List Nat) (result : (List Nat × List Nat)) : Prop :=
  let evens := result.1
  let odds := result.2
  evens.Sublist nums ∧
  odds.Sublist nums ∧
  (∀ (x : Nat), x ∈ evens ↔ (x ∈ nums ∧ isEven x)) ∧
  (∀ (x : Nat), x ∈ odds ↔ (x ∈ nums ∧ isOdd x)) ∧
  (∀ (x : Nat), x ∈ evens → x ∉ odds)
end Specs

section Impl
method PartitionEvenOdd (nums : List Nat)
  return (result : (List Nat × List Nat))
  require precondition nums
  ensures postcondition nums result
  do
  pure ([], [])  -- placeholder

end Impl

section TestCases
-- Test case 1: empty list
-- Edge case: valid because empty list is Nodup

def test1_nums : List Nat := []
def test1_Expected : (List Nat × List Nat) := ([], [])

-- Test case 2: singleton even (0)

def test2_nums : List Nat := [0]
def test2_Expected : (List Nat × List Nat) := ([0], [])

-- Test case 3: singleton odd (1)

def test3_nums : List Nat := [1]
def test3_Expected : (List Nat × List Nat) := ([], [1])

-- Test case 4: mixed small list

def test4_nums : List Nat := [0, 1, 2, 3, 4, 5]
def test4_Expected : (List Nat × List Nat) := ([0, 2, 4], [1, 3, 5])

-- Test case 5: all even

def test5_nums : List Nat := [2, 4, 6, 8]
def test5_Expected : (List Nat × List Nat) := ([2, 4, 6, 8], [])

-- Test case 6: all odd

def test6_nums : List Nat := [1, 3, 5, 7, 9]
def test6_Expected : (List Nat × List Nat) := ([], [1, 3, 5, 7, 9])

-- Test case 7: alternating starting with odd

def test7_nums : List Nat := [1, 0, 3, 2, 5, 4]
def test7_Expected : (List Nat × List Nat) := ([0, 2, 4], [1, 3, 5])

-- Test case 8: non-trivial order

def test8_nums : List Nat := [10, 7, 6, 1, 3, 2]
def test8_Expected : (List Nat × List Nat) := ([10, 6, 2], [7, 1, 3])

-- Test case 9: includes larger numbers and 0

def test9_nums : List Nat := [100, 101, 0, 99, 42]
def test9_Expected : (List Nat × List Nat) := ([100, 0, 42], [101, 99])

-- Recommend to validate: empty input, singleton lists (0 and 1), mixed parity with preserved order
end TestCases
