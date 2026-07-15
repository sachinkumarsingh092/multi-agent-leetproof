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
    MergeIntervals: merge all overlapping integer intervals.

    Natural language breakdown:
    1. The input is a list of closed intervals, where each interval is a pair (start, end) of integers.
    2. Each interval is well-formed: start ≤ end.
    3. Intervals are interpreted as closed *continuous* intervals (over rational points), not just sets of integer points.
    4. Two intervals overlap if they share at least one point.
    5. The output is a list of closed intervals (start, end) of integers.
    6. The output intervals are well-formed.
    7. The output list is sorted by nondecreasing start values.
    8. The output intervals are non-overlapping: for adjacent intervals prev and next, prev.end < next.start.
    9. The output covers exactly the same set of rational points as the input (same union).
    10. The output is a canonical merged form: between any two consecutive output intervals there is an actual uncovered gap
        (some rational point strictly between them is not covered by the input).
-/

section Specs
-- An interval is represented as (start, end).
abbrev Interval := Prod Int Int

def intervalStart (iv : Interval) : Int := iv.1

def intervalEnd (iv : Interval) : Int := iv.2

-- Well-formed intervals have start ≤ end.
def intervalWellFormed (iv : Interval) : Prop :=
  intervalStart iv ≤ intervalEnd iv

-- Convert an Int endpoint to a rational point.
def intToRat (z : Int) : Rat :=
  Rat.ofInt z

-- Rational point membership in a closed interval.
def inIntervalRat (x : Rat) (iv : Interval) : Prop :=
  intToRat (intervalStart iv) ≤ x ∧ x ≤ intToRat (intervalEnd iv)

-- A rational point is covered by a list of intervals if it belongs to at least one interval.
def coversPointRat (intervals : List Interval) (x : Rat) : Prop :=
  ∃ (i : Nat), i < intervals.length ∧ inIntervalRat x (intervals[i]!)

-- List is sorted by nondecreasing start values.
def sortedByStart (intervals : List Interval) : Prop :=
  ∀ (i : Nat), i + 1 < intervals.length →
    intervalStart (intervals[i]!) ≤ intervalStart (intervals[i + 1]!)

-- Adjacent intervals are strictly separated: prev.end < next.start.
-- This forbids overlap and also forbids touching (since touching implies equality, not strict <).
def separatedAdjacent (intervals : List Interval) : Prop :=
  ∀ (i : Nat), i + 1 < intervals.length →
    intervalEnd (intervals[i]!) < intervalStart (intervals[i + 1]!)

-- All intervals in a list are well-formed.
def allWellFormed (intervals : List Interval) : Prop :=
  ∀ (i : Nat), i < intervals.length → intervalWellFormed (intervals[i]!)

-- Canonical-gap property: between any two consecutive output intervals, there exists a rational point
-- strictly between them that is not covered by the *input*.
-- This rules out gratuitous splitting of a continuously covered region.
def hasUncoveredGapWrtInput (input : List Interval) (result : List Interval) : Prop :=
  ∀ (i : Nat), i + 1 < result.length →
    ∃ (q : Rat),
      intToRat (intervalEnd (result[i]!)) < q ∧
      q < intToRat (intervalStart (result[i + 1]!)) ∧
      ¬ coversPointRat input q

-- Preconditions: input intervals are well-formed.
def precondition (intervals : List Interval) : Prop :=
  allWellFormed intervals

-- Postconditions:
-- 1) result intervals are well-formed
-- 2) result is sorted by start
-- 3) result intervals are strictly separated (no overlap)
-- 4) coverage equivalence over rational points (continuous interpretation)
-- 5) canonical-gap property with respect to the input (prevents non-canonical splitting)
def postcondition (intervals : List Interval) (result : List Interval) : Prop :=
  allWellFormed result ∧
  sortedByStart result ∧
  separatedAdjacent result ∧
  (∀ (x : Rat), coversPointRat intervals x ↔ coversPointRat result x) ∧
  hasUncoveredGapWrtInput intervals result
end Specs

section Impl
method MergeIntervals (intervals : List Interval)
  return (result : List Interval)
  require precondition intervals
  ensures postcondition intervals result
  do
  pure []

end Impl

section TestCases
-- Test case 1: example-like overlapping chain that merges into three intervals
-- [(1,3),(2,6),(8,10),(15,18)] -> [(1,6),(8,10),(15,18)]
def test1_intervals : List Interval :=
  [((1 : Int), (3 : Int)), ((2 : Int), (6 : Int)), ((8 : Int), (10 : Int)), ((15 : Int), (18 : Int))]
def test1_Expected : List Interval :=
  [((1 : Int), (6 : Int)), ((8 : Int), (10 : Int)), ((15 : Int), (18 : Int))]

-- Test case 2: empty input
def test2_intervals : List Interval := []
def test2_Expected : List Interval := []

-- Test case 3: singleton interval
def test3_intervals : List Interval := [((5 : Int), (7 : Int))]
def test3_Expected : List Interval := [((5 : Int), (7 : Int))]

-- Test case 4: already separated and sorted (includes 0 boundary)
def test4_intervals : List Interval :=
  [((0 : Int), (0 : Int)), ((3 : Int), (4 : Int)), ((10 : Int), (12 : Int))]
def test4_Expected : List Interval :=
  [((0 : Int), (0 : Int)), ((3 : Int), (4 : Int)), ((10 : Int), (12 : Int))]

-- Test case 5: touching intervals should NOT be merged under strict-overlap semantics
-- [1,2] and [3,5] do not overlap as closed continuous intervals
def test5_intervals : List Interval := [((1 : Int), (2 : Int)), ((3 : Int), (5 : Int))]
def test5_Expected : List Interval := [((1 : Int), (2 : Int)), ((3 : Int), (5 : Int))]

-- Test case 6: nested intervals
def test6_intervals : List Interval :=
  [((1 : Int), (10 : Int)), ((2 : Int), (3 : Int)), ((4 : Int), (8 : Int))]
def test6_Expected : List Interval := [((1 : Int), (10 : Int))]

-- Test case 7: unsorted input requiring sort before merge
-- [(5,7),(1,2),(2,4)] -> [(1,4),(5,7)]
def test7_intervals : List Interval :=
  [((5 : Int), (7 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (4 : Int))]
def test7_Expected : List Interval := [((1 : Int), (4 : Int)), ((5 : Int), (7 : Int))]

-- Test case 8: negative endpoints and overlap (includes -1)
def test8_intervals : List Interval :=
  [((-10 : Int), (-5 : Int)), ((-7 : Int), (0 : Int)), ((2 : Int), (2 : Int))]
def test8_Expected : List Interval := [((-10 : Int), (0 : Int)), ((2 : Int), (2 : Int))]

-- Test case 9: duplicates and a separated point interval
def test9_intervals : List Interval :=
  [((1 : Int), (3 : Int)), ((1 : Int), (3 : Int)), ((4 : Int), (4 : Int))]
def test9_Expected : List Interval := [((1 : Int), (3 : Int)), ((4 : Int), (4 : Int))]

-- Test case 10: exposes previous non-uniqueness bug; a single interval must not be split
-- [(1,6)] must stay as [(1,6)]
def test10_intervals : List Interval := [((1 : Int), (6 : Int))]
def test10_Expected : List Interval := [((1 : Int), (6 : Int))]

-- Recommend to validate: test1_intervals, test5_intervals, test7_intervals
end TestCases
