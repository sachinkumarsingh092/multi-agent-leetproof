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
    verina_basic_57: Count how many integers in an array are strictly less than a given threshold.
    Natural language breakdown:
    1. Input is an array of integers `numbers` and an integer `threshold`.
    2. An element of the array is counted if and only if its value is strictly less than `threshold`.
    3. The output is a natural number giving the total number of counted elements.
    4. The function must work for any array (including empty) and any integer threshold.
-/

section Specs
-- We specify the count as the cardinality of the set of valid indices whose elements are < threshold.
-- This uses only standard Mathlib/Lean constructions: `Finset.range`, `Finset.filter`, and `Finset.card`.

def precondition (numbers : Array Int) (threshold : Int) : Prop :=
  True

def postcondition (numbers : Array Int) (threshold : Int) (result : Nat) : Prop :=
  result = ((Finset.range numbers.size).filter (fun (i : Nat) => numbers[i]! < threshold)).card ∧
  result ≤ numbers.size
end Specs

section Impl
method CountLessThan (numbers : Array Int) (threshold : Int)
  return (result : Nat)
  require precondition numbers threshold
  ensures postcondition numbers threshold result
  do
  pure 0

prove_correct CountLessThan by sorry
end Impl

section TestCases
-- Test case 1: empty array
-- numbers = [], threshold = 0 => count = 0

def test1_numbers : Array Int := #[]
def test1_threshold : Int := 0
def test1_Expected : Nat := 0

-- Test case 2: singleton where element is less
-- numbers = [-1], threshold = 0 => count = 1

def test2_numbers : Array Int := #[-1]
def test2_threshold : Int := 0
def test2_Expected : Nat := 1

-- Test case 3: singleton where element is not less (equal)
-- numbers = [5], threshold = 5 => count = 0

def test3_numbers : Array Int := #[5]
def test3_threshold : Int := 5
def test3_Expected : Nat := 0

-- Test case 4: mixed positives, threshold in the middle
-- numbers = [1,2,3,4], threshold = 3 => count = 2

def test4_numbers : Array Int := #[1, 2, 3, 4]
def test4_threshold : Int := 3
def test4_Expected : Nat := 2

-- Test case 5: all elements less than threshold
-- numbers = [1,2,3], threshold = 10 => count = 3

def test5_numbers : Array Int := #[1, 2, 3]
def test5_threshold : Int := 10
def test5_Expected : Nat := 3

-- Test case 6: no element less than threshold
-- numbers = [1,2,3], threshold = -5 => count = 0

def test6_numbers : Array Int := #[1, 2, 3]
def test6_threshold : Int := -5
def test6_Expected : Nat := 0

-- Test case 7: duplicates counted separately
-- numbers = [2,2,2], threshold = 3 => count = 3

def test7_numbers : Array Int := #[2, 2, 2]
def test7_threshold : Int := 3
def test7_Expected : Nat := 3

-- Test case 8: mix of negatives, zero, positives
-- numbers = [-3,-2,-1,0,1], threshold = -1 => count = 2

def test8_numbers : Array Int := #[-3, -2, -1, 0, 1]
def test8_threshold : Int := -1
def test8_Expected : Nat := 2

-- Test case 9: threshold is the minimum Int-like extreme used in tests
-- numbers = [-100, 0, 100], threshold = -100 => count = 0

def test9_numbers : Array Int := #[-100, 0, 100]
def test9_threshold : Int := -100
def test9_Expected : Nat := 0
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Nat) :
  result ≠ test9_Expected →
  ¬ postcondition test9_numbers test9_threshold result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
