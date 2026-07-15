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
    SingleNumber: in a non-empty array of integers, every element appears exactly twice except for one element that appears once; return that single element.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array `nums` of integers and it is non-empty.
    2. There exists an integer `s` that occurs in `nums` exactly once.
    3. Every other integer occurring in `nums` occurs in `nums` exactly twice.
    4. The output must be the unique integer that occurs exactly once.
-/

section Specs
-- Helper predicate: an element occurs exactly once in an array.
def occursOnce (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 1

-- Helper predicate: an element occurs exactly twice in an array.
def occursTwice (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 2

-- Precondition: the array is non-empty and has exactly one element with count 1,
-- and all other elements appearing in the array have count 2.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∃ s : Int,
    s ∈ nums ∧
    occursOnce nums s ∧
    (∀ y : Int, y ∈ nums → y ≠ s → occursTwice nums y))

-- Postcondition: result is the unique element that occurs once.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  result ∈ nums ∧
  occursOnce nums result ∧
  (∀ y : Int, y ∈ nums → occursOnce nums y → y = result)
end Specs

section Impl
method SingleNumber (nums : Array Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure 0

end Impl

section TestCases
-- Test case 1: Example 1
-- Input: nums = [2,2,1]
-- Output: 1

def test1_nums : Array Int := #[ (2 : Int), (2 : Int), (1 : Int) ]
def test1_Expected : Int := (1 : Int)

-- Test case 2: Example 2

def test2_nums : Array Int := #[ (4 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int) ]
def test2_Expected : Int := (4 : Int)

-- Test case 3: Example 3 (singleton array)

def test3_nums : Array Int := #[ (1 : Int) ]
def test3_Expected : Int := (1 : Int)

-- Test case 4: includes 0 (edge value) with unique 1

def test4_nums : Array Int := #[ (0 : Int), (1 : Int), (0 : Int) ]
def test4_Expected : Int := (1 : Int)

-- Test case 5: includes negative number as the unique element

def test5_nums : Array Int := #[ (-1 : Int), (2 : Int), (2 : Int) ]
def test5_Expected : Int := (-1 : Int)

-- Test case 6: unique element in the middle, multiple pairs

def test6_nums : Array Int := #[ (5 : Int), (5 : Int), (6 : Int), (7 : Int), (7 : Int) ]
def test6_Expected : Int := (6 : Int)

-- Test case 7: larger odd length, unique element at end

def test7_nums : Array Int := #[ (1 : Int), (1 : Int), (2 : Int), (2 : Int), (3 : Int), (3 : Int), (4 : Int) ]
def test7_Expected : Int := (4 : Int)

-- Test case 8: unique element at start

def test8_nums : Array Int := #[ (9 : Int), (8 : Int), (8 : Int), (7 : Int), (7 : Int) ]
def test8_Expected : Int := (9 : Int)

-- Test case 9: singleton array containing 0

def test9_nums : Array Int := #[ (0 : Int) ]
def test9_Expected : Int := (0 : Int)
end TestCases
