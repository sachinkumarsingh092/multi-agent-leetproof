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
    PeakValleyPattern: Determine whether a list of integers follows a peak-valley pattern.
    Natural language breakdown:
    1. The input is a list of integers.
    2. The output is a boolean-like integer value represented as Bool: true or false.
    3. The list follows a peak-valley pattern iff there exists a peak position p such that:
       a. p is not the first index and not the last index (both parts are non-empty).
       b. The list is strictly increasing on consecutive elements from index 0 up to index p.
       c. The list is strictly decreasing on consecutive elements from index p down to the end.
    4. Strictly increasing means every adjacent pair in the increasing region satisfies a[i] < a[i+1].
    5. Strictly decreasing means every adjacent pair in the decreasing region satisfies a[i] > a[i+1].
    6. Lists with length < 3 cannot satisfy the pattern (cannot have non-empty increasing and decreasing parts).
    7. Any equal adjacent elements violate strictness and thus make the pattern false.
-/

section Specs
-- Helper predicate: consecutive strict increase up to peak index p.
-- We require that for every i < p, the adjacent elements i and i+1 strictly increase.
-- The extra guard (i + 1 < lst.length) makes indexing safe for List.get!.
def StrictIncTo (lst : List Int) (p : Nat) : Prop :=
  ∀ (i : Nat), i < p → i + 1 < lst.length → lst[i]! < lst[i + 1]!

-- Helper predicate: consecutive strict decrease starting at peak index p.
-- For every i ≥ p (up to the last adjacent pair), the adjacent elements i and i+1 strictly decrease.
def StrictDecFrom (lst : List Int) (p : Nat) : Prop :=
  ∀ (i : Nat), p ≤ i → i + 1 < lst.length → lst[i]! > lst[i + 1]!

-- Core mathematical notion of a peak-valley list.
-- There exists an interior peak index p with a strict increase before it and strict decrease after it.
def PeakValley (lst : List Int) : Prop :=
  ∃ (p : Nat),
    0 < p ∧
    p + 1 < lst.length ∧
    StrictIncTo lst p ∧
    StrictDecFrom lst p

def precondition (lst : List Int) : Prop :=
  True

def postcondition (lst : List Int) (result : Bool) : Prop :=
  result = true ↔ PeakValley lst
end Specs

section Impl
method PeakValleyPattern (lst : List Int)
  return (result : Bool)
  require precondition lst
  ensures postcondition lst result
  do
  pure false

prove_correct PeakValleyPattern by sorry
end Impl

section TestCases
-- Test case 1: example from the problem statement
def test1_lst : List Int := [1, 3, 5, 4, 2]
def test1_Expected : Bool := true

-- Test case 2: strictly increasing only
def test2_lst : List Int := [1, 2, 3]
def test2_Expected : Bool := false

-- Test case 3: strictly decreasing only
def test3_lst : List Int := [5, 4, 3]
def test3_Expected : Bool := false

-- Test case 4: has an equality plateau (not strict)
def test4_lst : List Int := [1, 2, 2, 1]
def test4_Expected : Bool := false

-- Test case 5: empty list (degenerate)
def test5_lst : List Int := []
def test5_Expected : Bool := false

-- Test case 6: singleton list (degenerate)
def test6_lst : List Int := [7]
def test6_Expected : Bool := false

-- Test case 7: length 2 list (cannot have both parts non-empty)
def test7_lst : List Int := [1, 0]
def test7_Expected : Bool := false

-- Test case 8: minimal valid peak-valley with length 3
def test8_lst : List Int := [1, 3, 2]
def test8_Expected : Bool := true

-- Test case 9: includes negative integers and a clear peak
def test9_lst : List Int := [-3, -1, 0, -2, -5]
def test9_Expected : Bool := true

-- Test case 10: peak-like shape but not strict on the decreasing side (equal adjacent)
def test10_lst : List Int := [0, 2, 4, 4, 1]
def test10_Expected : Bool := false
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test10' (result : Bool) :
  result ≠ test10_Expected →
  ¬ postcondition test10_lst result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test10_Expected]) (config := { numInst := 100000 })
