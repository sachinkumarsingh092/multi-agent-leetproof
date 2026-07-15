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
    MergeIntervals: merge all overlapping closed intervals in a sorted array.
    Natural language breakdown:
    1. The input is an array of intervals, each interval is a pair (start, end) of integers.
    2. Each interval is interpreted as a closed interval [start, end].
    3. Valid intervals satisfy start ≤ end.
    4. The input is sorted lexicographically by (start, end) in nondecreasing order.
    5. Two intervals overlap if the next start is ≤ the previous end (touching at a point counts as overlap).
    6. The output is an array of intervals that are pairwise non-overlapping (separated) and sorted.
    7. The output intervals cover exactly the same set of integer points as the input intervals.
    8. The output is a canonical merging: it is non-overlapping and each interval is maximal (cannot be extended without losing correctness).
    Your algorithm should run in **O(n)** time and **O(n)** extra space.
-/

section Specs
-- An interval is a pair (start, end).
abbrev Interval := Int × Int

-- Accessors (keep specs readable)
def istart (iv : Interval) : Int := iv.1

def iend (iv : Interval) : Int := iv.2

-- Membership of an integer point in a closed interval
-- Uses Int inequalities; we reason over integer points only.
def InInterval (x : Int) (iv : Interval) : Prop :=
  istart iv ≤ x ∧ x ≤ iend iv

-- An array is lex-sorted by (start, end)
-- We use adjacent-pair monotonicity, which is simple and decidable.
def LexSortedIntervals (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size →
    (istart a[i]! < istart a[i+1]! ) ∨
    (istart a[i]! = istart a[i+1]! ∧ iend a[i]! ≤ iend a[i+1]! ) ∨
    (istart a[i]! = istart a[i+1]! ∧ iend a[i]! = iend a[i+1]! )

-- Validity: every interval has start ≤ end
-- (Input may be empty; then this is trivially true.)
def AllValid (a : Array Interval) : Prop :=
  ∀ (i : Nat), i < a.size → istart a[i]! ≤ iend a[i]!

-- Output property: intervals are strictly separated (no overlap, no touching)
-- i.e., end_i < start_{i+1}
def StrictlyNonOverlapping (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → iend a[i]! < istart a[i+1]!

-- Output is sorted by starts (and ends as tiebreaker is vacuous under strict separation,
-- but we also require nondecreasing starts for robustness).
def NondecreasingStarts (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → istart a[i]! ≤ istart a[i+1]!

-- Coverage equivalence over integer points.
-- x is covered by an array iff it is in some interval of the array.
def CoveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ (i : Nat), i < a.size ∧ InInterval x a[i]!

-- Maximality / canonical merge: no interval in the result can be extended while preserving
-- non-overlap and coverage equivalence.
-- We phrase this as: for each resulting interval, its start is the minimum covered point within
-- its connected component and its end is the maximum covered point within that component.
-- A simpler characterization that avoids heavy connected-component reasoning:
--   - Every result interval's start is covered by the input.
--   - Every result interval's end is covered by the input.
--   - Every integer point between start and end is covered by the input.
-- Together with strict non-overlap, this pins down the unique merged output.
def IntervalIsTight (input : Array Interval) (iv : Interval) : Prop :=
  CoveredBy (istart iv) input ∧
  CoveredBy (iend iv) input ∧
  (∀ (x : Int), istart iv ≤ x ∧ x ≤ iend iv → CoveredBy x input)

-- Preconditions and postconditions

def precondition (intervals : Array Interval) : Prop :=
  AllValid intervals ∧ LexSortedIntervals intervals

def postcondition (intervals : Array Interval) (result : Array Interval) : Prop :=
  AllValid result ∧
  NondecreasingStarts result ∧
  StrictlyNonOverlapping result ∧
  -- exact coverage equivalence
  (∀ (x : Int), CoveredBy x result ↔ CoveredBy x intervals) ∧
  -- canonical/tight intervals (prevents splitting into smaller disjoint intervals)
  (∀ (i : Nat), i < result.size → IntervalIsTight intervals result[i]!)
end Specs

section Impl
method MergeIntervals (intervals : Array Interval)
  return (result : Array Interval)
  require precondition intervals
  ensures postcondition intervals result
  do
    if intervals.size = 0 then
      return #[]
    else
      let mut result : Array Interval := #[]
      let mut curStart : Int := istart intervals[0]!
      let mut curEnd : Int := iend intervals[0]!
      let mut i : Nat := 1
      while i < intervals.size
        -- Bounds: i stays in [1, intervals.size]; init: i=1; pres: i increments up to size; suff: with done_with gives i=size
        invariant "bounds" 1 ≤ i ∧ i ≤ intervals.size
        -- Working interval is valid (start ≤ end); init: from AllValid on intervals[0]; pres: maintained by merge logic
        invariant "cur_valid" curStart ≤ curEnd
        -- All finalized result intervals are valid; init: #[] trivially valid; pres: we push valid (curStart,curEnd)
        invariant "res_valid" AllValid result
        -- Result intervals have nondecreasing starts; init: trivial for #[]; pres: gap_to_cur ensures ordering
        invariant "res_sorted" NondecreasingStarts result
        -- Result intervals are strictly non-overlapping; init: trivial; pres: gap ensures separation
        invariant "res_sep" StrictlyNonOverlapping result
        -- Last finalized end < working start; needed to establish non-overlap when pushing
        invariant "gap_to_cur" result.size > 0 → iend (result.back!) < curStart
        -- Coverage: finalized union working interval covers exactly first i input intervals
        -- init: working = intervals[0], covers j<1; pres: extending or starting new preserves coverage; suff: at exit covers all
        invariant "cov" ∀ (x : Int), (CoveredBy x result ∨ (curStart ≤ x ∧ x ≤ curEnd)) ↔ (∃ j : Nat, j < i ∧ InInterval x intervals[j]!)
        -- Every finalized interval is tight w.r.t. full input; init: none finalized; pres: working was tight before finalization
        invariant "tight_fin" ∀ (k : Nat), k < result.size → IntervalIsTight intervals result[k]!
        -- Working interval is tight w.r.t. full input; init: intervals[0] is tight; pres: extending preserves tightness
        invariant "tight_work" IntervalIsTight intervals (curStart, curEnd)
        -- When loop exits, we've processed all intervals
        done_with i = intervals.size
        decreasing intervals.size - i
      do
        let iv := intervals[i]!
        let s := istart iv
        let e := iend iv
        if s <= curEnd then
          if e > curEnd then
            curEnd := e
        else
          result := result.push (curStart, curEnd)
          curStart := s
          curEnd := e
        i := i + 1
      result := result.push (curStart, curEnd)
      return result
end Impl

section TestCases
-- Test case 1: Example 1 from prompt
-- intervals = [[1,3],[2,6],[8,10],[15,18]] -> [[1,6],[8,10],[15,18]]
def test1_intervals : Array Interval := #[(1,3),(2,6),(8,10),(15,18)]
def test1_Expected : Array Interval := #[(1,6),(8,10),(15,18)]

-- Test case 2: Example 2 from prompt (touching counts as overlap)
def test2_intervals : Array Interval := #[(1,4),(4,5)]
def test2_Expected : Array Interval := #[(1,5)]

-- Test case 3: Empty input

def test3_intervals : Array Interval := #[]
def test3_Expected : Array Interval := #[]

-- Test case 4: Single interval

def test4_intervals : Array Interval := #[(7,7)]
def test4_Expected : Array Interval := #[(7,7)]

-- Test case 5: Already non-overlapping (strictly separated)

def test5_intervals : Array Interval := #[(1,2),(4,4),(6,9)]
def test5_Expected : Array Interval := #[(1,2),(4,4),(6,9)]

-- Test case 6: Chain of overlaps that collapses into one

def test6_intervals : Array Interval := #[(1,3),(2,4),(4,8),(8,9)]
def test6_Expected : Array Interval := #[(1,9)]

-- Test case 7: Same start, increasing ends (lex sorted) merges

def test7_intervals : Array Interval := #[(1,2),(1,3),(1,10)]
def test7_Expected : Array Interval := #[(1,10)]

-- Test case 8: Negative coordinates

def test8_intervals : Array Interval := #[(-10,-5),(-6,-1),(0,0)]
def test8_Expected : Array Interval := #[(-10,-1),(0,0)]

-- Test case 9: Nested intervals

def test9_intervals : Array Interval := #[(1,10),(2,3),(4,5),(6,7)]
def test9_Expected : Array Interval := #[(1,10)]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MergeIntervals test1_intervals).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MergeIntervals test2_intervals).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MergeIntervals test3_intervals).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MergeIntervals test4_intervals).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MergeIntervals test5_intervals).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MergeIntervals test6_intervals).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MergeIntervals test7_intervals).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MergeIntervals test8_intervals).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MergeIntervals test9_intervals).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MergeIntervals (config := { maxMs := some 20000 })
end Pbt
