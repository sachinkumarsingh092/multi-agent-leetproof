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
    SecondSmallest: find the second-smallest integer in an array.
    Natural language breakdown:
    1. The input is an array s : Array Int.
    2. The array must contain at least two elements.
    3. The array must contain at least two distinct values.
    4. Let m be the smallest value occurring in s.
    5. The result is a value r occurring in s such that m < r.
    6. Among all values x occurring in s with m < x, the result r is minimal (i.e., r ≤ x for all such x).
    7. The computation must not modify the input array (arrays are immutable in this setting).
-/

section Specs
-- Membership predicate for arrays, phrased using Nat indices (preferred for specs).
def InArray (s : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < s.size ∧ s[i]! = x

-- At least two distinct elements occur in the array.
def HasTwoDistinct (s : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat),
    i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!

-- Preconditions: size ≥ 2 and at least two distinct values.
def precondition (s : Array Int) : Prop :=
  s.size ≥ 2 ∧ HasTwoDistinct s

-- Postcondition: result is the least element strictly greater than the minimum element of s.
def postcondition (s : Array Int) (result : Int) : Prop :=
  ∃ (m : Int),
    s.min? = some m ∧
    InArray s m ∧
    (∀ (x : Int), InArray s x → m ≤ x) ∧
    InArray s result ∧
    m < result ∧
    (∀ (x : Int), InArray s x → m < x → result ≤ x)
end Specs

section Impl
method SecondSmallest (s : Array Int)
  return (result : Int)
  require precondition s
  ensures postcondition s result
  do
  pure 0

prove_correct SecondSmallest by sorry
end Impl

section TestCases
-- Test case 1: typical unsorted array
-- s = [3, 1, 2] => second-smallest is 2

def test1_s : Array Int := #[3, 1, 2]
def test1_Expected : Int := 2

-- Test case 2: minimal valid size (ascending)
def test2_s : Array Int := #[1, 2]
def test2_Expected : Int := 2

-- Test case 3: minimal valid size (descending)
def test3_s : Array Int := #[2, 1]
def test3_Expected : Int := 2

-- Test case 4: duplicates of the minimum

def test4_s : Array Int := #[0, 0, 1]
def test4_Expected : Int := 1

-- Test case 5: all negative values

def test5_s : Array Int := #[-3, -1, -2]
def test5_Expected : Int := -2

-- Test case 6: contains -1, 0, 1 (boundary-style values around zero)

def test6_s : Array Int := #[-1, 0, 1]
def test6_Expected : Int := 0

-- Test case 7: many duplicates with a single larger value

def test7_s : Array Int := #[5, 5, 5, 6]
def test7_Expected : Int := 6

-- Test case 8: minimum occurs multiple times and is not adjacent

def test8_s : Array Int := #[10, -10, 0, -10, 7]
def test8_Expected : Int := 0

-- Test case 9: longer descending array including 0

def test9_s : Array Int := #[4, 3, 2, 1, 0]
def test9_Expected : Int := 1
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test9' (result : Int) :
  result ≠ test9_Expected →
  ¬ postcondition test9_s result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test9_Expected]) (config := { numInst := 100000 })
