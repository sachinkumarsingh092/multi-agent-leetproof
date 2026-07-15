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
    MinRightShiftsToSort: compute the minimum number of right shifts needed to make a list of distinct positive integers sorted ascending.

    A right shift on a list of length n moves each element at index i to index (i+1) % n.
    Equivalently, it performs a cyclic rotation where the last element becomes first.

    Natural language breakdown:
    1. Input is a list of integers `nums` whose elements are positive and pairwise distinct.
    2. A right shift by k positions is a cyclic rotation by k (modulo the list length).
    3. The goal is to make the list sorted in nondecreasing (ascending) order.
    4. If the list is already sorted, the answer is 0.
    5. If some number of right shifts can make the list sorted, the answer is the minimum such number.
    6. If no right shift can make the list sorted, the answer is -1.
    7. For lists of length 0 or 1, the list is already sorted and the answer is 0.
-/

section Specs
-- A computable notion of ascending sortedness (using Mathlib's `List.Sorted`).
def isSortedAsc (l : List Int) : Prop :=
  l.Sorted (· ≤ ·)

-- Right shift by k: implemented as a left-rotation by (len - (k mod len)).
-- For empty lists, a shift leaves the list unchanged.
def rightShift (l : List Int) (k : Nat) : List Int :=
  if h : l.length = 0 then
    l
  else
    let n := l.length
    l.rotate (n - (k % n))

-- Preconditions from the problem statement: distinct, positive integers.
def precondition (nums : List Int) : Prop :=
  nums.Nodup ∧ ∀ (x : Int), x ∈ nums → 0 < x

-- Postcondition: either result = -1 and no right shift sorts the list,
-- or result is a nonnegative integer representing the minimum right-shift count that sorts it.
def postcondition (nums : List Int) (result : Int) : Prop :=
  (result = -1 ∧
    (nums.length = 0 → False) ∧
    (∀ (k : Nat), k < nums.length → ¬ isSortedAsc (rightShift nums k)))
  ∨
  (0 ≤ result ∧
    (nums.length = 0 → result = 0) ∧
    (nums.length > 0 → result.toNat < nums.length) ∧
    isSortedAsc (rightShift nums result.toNat) ∧
    (∀ (k : Nat), k < result.toNat → ¬ isSortedAsc (rightShift nums k)))
end Specs

section Impl
method MinRightShiftsToSort (nums : List Int)
  return (result : Int)
  require precondition nums
  ensures postcondition nums result
  do
  pure (-1)  -- placeholder

end Impl

section TestCases
-- Test case 1: classic rotation-sorted example; needs 2 right shifts to become sorted.
def test1_nums : List Int := [3, 4, 5, 1, 2]
def test1_Expected : Int := 2

-- Test case 2: already sorted.
def test2_nums : List Int := [1, 2, 3, 4, 5]
def test2_Expected : Int := 0

-- Test case 3: impossible to sort by right shifts.
def test3_nums : List Int := [2, 1, 3]
def test3_Expected : Int := -1

-- Test case 4: empty list (degenerate, vacuously sorted).
def test4_nums : List Int := []
def test4_Expected : Int := 0

-- Test case 5: singleton list.
def test5_nums : List Int := [7]
def test5_Expected : Int := 0

-- Test case 6: length 2, one shift needed.
def test6_nums : List Int := [2, 1]
def test6_Expected : Int := 1

-- Test case 7: rotation-sorted with answer 1.
def test7_nums : List Int := [2, 3, 4, 5, 1]
def test7_Expected : Int := 1

-- Test case 8: rotation-sorted with answer 3.
def test8_nums : List Int := [4, 1, 2, 3]
def test8_Expected : Int := 3

-- Test case 9: another impossible arrangement.
def test9_nums : List Int := [1, 3, 2]
def test9_Expected : Int := -1
end TestCases
