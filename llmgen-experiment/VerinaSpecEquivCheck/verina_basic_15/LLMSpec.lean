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
    HasConsecutivePair: Determine whether an array of integers contains at least one pair of consecutive numbers.
    Natural language breakdown:
    1. The input is an array a of integers; it may be empty or non-empty.
    2. A "consecutive pair" means two adjacent elements a[i] and a[i+1] such that a[i] + 1 = a[i+1].
    3. The function returns true exactly when there exists some index i with i+1 within bounds and a[i] + 1 = a[i+1].
    4. If the array has size 0 or 1, then no adjacent pair exists, so the result must be false.
    5. There are no additional input constraints.
-/

section Specs
-- Existence of an index with an adjacent consecutive step by +1.
def hasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ hasConsecutivePair a) ∧
  (result = false ↔ ¬ hasConsecutivePair a)
end Specs

section Impl
method HasConsecutivePair (a : Array Int)
  return (result : Bool)
  require precondition a
  ensures postcondition a result
  do
  pure false

end Impl

section TestCases
-- Test case 1: typical case with a consecutive pair at the beginning
-- a = [1, 2, 4] has 1+1=2

def test1_a : Array Int := #[1, 2, 4]
def test1_Expected : Bool := true

-- Test case 2: empty array has no adjacent indices

def test2_a : Array Int := #[]
def test2_Expected : Bool := false

-- Test case 3: singleton array has no adjacent indices

def test3_a : Array Int := #[7]
def test3_Expected : Bool := false

-- Test case 4: size-2 array that is consecutive

def test4_a : Array Int := #[5, 6]
def test4_Expected : Bool := true

-- Test case 5: size-2 array that is not consecutive (descending)

def test5_a : Array Int := #[6, 5]
def test5_Expected : Bool := false

-- Test case 6: negative integers can be consecutive

def test6_a : Array Int := #[-2, -1]
def test6_Expected : Bool := true

-- Test case 7: consecutive pair occurs in the middle
-- a = [10, 12, 13, 20] has 12+1=13

def test7_a : Array Int := #[10, 12, 13, 20]
def test7_Expected : Bool := true

-- Test case 8: no consecutive pairs in a longer array

def test8_a : Array Int := #[0, 2, 4, 7]
def test8_Expected : Bool := false

-- Test case 9: multiple consecutive pairs exist

def test9_a : Array Int := #[0, 1, 2, 3]
def test9_Expected : Bool := true
end TestCases
