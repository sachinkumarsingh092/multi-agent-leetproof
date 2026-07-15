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
    MaxSpanAfterRemovingOneInterval: given a non-empty list of intervals, remove exactly one interval and return the maximum possible span of the remaining intervals.

    Natural language breakdown:
    1. The input is a non-empty list of intervals, each interval represented as a pair (l, r) of natural numbers.
    2. Each interval is well-formed: its left endpoint l is less than or equal to its right endpoint r.
    3. Removing exactly one interval means choosing an index i within bounds and deleting the element at index i, preserving the order of all other intervals.
    4. The span of a list of intervals is defined as:
       - 0 if the list is empty
       - otherwise, (maximum right endpoint among the intervals) minus (minimum left endpoint among the intervals).
    5. The required output is the maximum span obtainable among all choices of removing exactly one interval.
    6. If the input list has exactly one interval, removing it leaves the empty list, whose span is 0.
-/

section Specs
-- Remove the element at index i, keeping all other elements in order.
-- Defined using take/drop (non-recursive).
def removeAt (intervals : List (Prod Nat Nat)) (i : Nat) : List (Prod Nat Nat) :=
  intervals.take i ++ intervals.drop (i + 1)

-- Minimum left endpoint of a non-empty interval list.
def minLeftOfNonempty (intervals : List (Prod Nat Nat)) : Nat :=
  match intervals with
  | [] => 0
  | h :: t =>
      t.foldl (fun (acc : Nat) (p : Prod Nat Nat) => Nat.min acc p.1) (init := h.1)

-- Maximum right endpoint of a non-empty interval list.
def maxRightOfNonempty (intervals : List (Prod Nat Nat)) : Nat :=
  match intervals with
  | [] => 0
  | h :: t =>
      t.foldl (fun (acc : Nat) (p : Prod Nat Nat) => Nat.max acc p.2) (init := h.2)

-- Span of an interval list. Empty list span is 0.
def span (intervals : List (Prod Nat Nat)) : Nat :=
  match intervals with
  | [] => 0
  | _ :: _ =>
      (maxRightOfNonempty intervals) - (minLeftOfNonempty intervals)

-- Interval well-formedness: l ≤ r.
def intervalWellFormed (p : Prod Nat Nat) : Prop :=
  p.1 ≤ p.2

-- Preconditions
-- 1) At least one interval is provided.
-- 2) Every interval is well-formed.
def precondition (intervals : List (Prod Nat Nat)) : Prop :=
  intervals.length > 0 ∧
  ∀ p : Prod Nat Nat, p ∈ intervals → intervalWellFormed p

-- Postcondition: result is the maximum span achievable by removing exactly one interval.
-- Achievability: result is attained by removing some valid index.
-- Maximality: result is at least as large as the span produced by removing any valid index.
def postcondition (intervals : List (Prod Nat Nat)) (result : Nat) : Prop :=
  (∃ i : Nat, i < intervals.length ∧ span (removeAt intervals i) = result) ∧
  (∀ i : Nat, i < intervals.length → span (removeAt intervals i) ≤ result)
end Specs

section Impl
method MaxSpanAfterRemovingOneInterval (intervals : List (Prod Nat Nat))
  return (result : Nat)
  require precondition intervals
  ensures postcondition intervals result
  do
  pure 0

prove_correct MaxSpanAfterRemovingOneInterval by sorry
end Impl

section TestCases
-- Test case 1: single interval; removing it yields empty list span = 0
-- intervals = [(0,0)]
def test1_intervals : List (Prod Nat Nat) := [(0, 0)]
def test1_Expected : Nat := 0

-- Test case 2: two disjoint intervals; remove either leaves a single interval with span 2
def test2_intervals : List (Prod Nat Nat) := [(0, 2), (5, 7)]
def test2_Expected : Nat := 2

-- Test case 3: three intervals; best is to remove one of the small ones, keeping span 10
def test3_intervals : List (Prod Nat Nat) := [(1, 4), (2, 3), (0, 10)]
def test3_Expected : Nat := 10

-- Test case 4: multiple small intervals; all removals yield same span 1
def test4_intervals : List (Prod Nat Nat) := [(0, 1), (0, 0), (1, 1)]
def test4_Expected : Nat := 1

-- Test case 5: includes a zero-length interval and a larger one
-- removing the large one yields span 0; removing the point yields span 5
def test5_intervals : List (Prod Nat Nat) := [(3, 3), (0, 5)]
def test5_Expected : Nat := 5

-- Test case 6: four intervals; best removal produces span 6
def test6_intervals : List (Prod Nat Nat) := [(0, 2), (3, 3), (4, 6), (1, 1)]
def test6_Expected : Nat := 6

-- Test case 7: identical intervals; removal does not change span (span is 1)
def test7_intervals : List (Prod Nat Nat) := [(1, 2), (1, 2), (1, 2)]
def test7_Expected : Nat := 1

-- Test case 8: includes endpoints 0 and 1 with a long interval; best keep the long one
-- removing (0,100) gives span 0; removing a point interval gives span 100
def test8_intervals : List (Prod Nat Nat) := [(0, 100), (1, 1), (0, 0)]
def test8_Expected : Nat := 100

-- Recommend to validate: singleton input, duplicate intervals, mixed point/long intervals
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test8' (result : Nat) :
  result ≠ test8_Expected →
  ¬ postcondition test8_intervals result := by
  try simp [loomAbstractionSimp]
  try dsimp at *
  try simp [*] at *
  aesop <;>
  plausible'_mut (seeds := #[test8_Expected]) (config := { numInst := 100000 })
