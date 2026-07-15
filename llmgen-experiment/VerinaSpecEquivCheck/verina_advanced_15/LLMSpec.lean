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
    IncreasingTripletSubsequence: decide whether a list of integers contains a strictly increasing subsequence of length 3.

    Natural language breakdown:
    1. Input is a list `nums` of integers.
    2. We look for three indices i, j, k into the list with i < j < k.
    3. All indices must be within bounds of the list.
    4. The values at those indices must be strictly increasing: nums[i] < nums[j] < nums[k].
    5. The output is a boolean: true iff such indices exist; false otherwise.
-/

section Specs
-- There exists a strictly increasing subsequence of length 3, witnessed by indices i<j<k.
-- We use `nums[i]!` with an explicit bound `k < nums.length` to ensure all accesses are in range.
def hasIncreasingTriplet (nums : List Int) : Prop :=
  ∃ (i : Nat) (j : Nat) (k : Nat),
    i < j ∧ j < k ∧ k < nums.length ∧
    nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!

def precondition (nums : List Int) : Prop :=
  True

def postcondition (nums : List Int) (result : Bool) : Prop :=
  result = true ↔ hasIncreasingTriplet nums
end Specs

section Impl
method IncreasingTripletSubsequence (nums : List Int)
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  pure false

end Impl

section TestCases
-- Test case 1: simple increasing list contains an increasing triplet
def test1_nums : List Int := [1, 2, 3, 4, 5]
def test1_Expected : Bool := true

-- Test case 2: empty list cannot contain a triplet
def test2_nums : List Int := []
def test2_Expected : Bool := false

-- Test case 3: singleton list cannot contain a triplet
def test3_nums : List Int := [42]
def test3_Expected : Bool := false

-- Test case 4: two elements cannot contain a triplet
def test4_nums : List Int := [1, 2]
def test4_Expected : Bool := false

-- Test case 5: exactly three elements, strictly increasing
def test5_nums : List Int := [1, 2, 3]
def test5_Expected : Bool := true

-- Test case 6: exactly three elements, not strictly increasing (duplicates)
def test6_nums : List Int := [1, 1, 2]
def test6_Expected : Bool := false

-- Test case 7: strictly decreasing list
def test7_nums : List Int := [5, 4, 3, 2, 1]
def test7_Expected : Bool := false

-- Test case 8: increasing triplet exists but not contiguous
def test8_nums : List Int := [2, 1, 5, 0, 4, 6]
def test8_Expected : Bool := true

-- Test case 9: includes negative values; triplet exists (-3 < -1 < 0)
def test9_nums : List Int := [-3, -2, -1, 0]
def test9_Expected : Bool := true

-- Test case 10: duplicates and plateaus prevent strict increase of length 3
def test10_nums : List Int := [1, 2, 2, 2, 3]
def test10_Expected : Bool := false
end TestCases
