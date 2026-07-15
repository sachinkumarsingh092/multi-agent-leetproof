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
    InsertInterval: insert a new closed interval into a sorted, non-overlapping array of closed intervals,
    merging overlaps, and return the resulting sorted, non-overlapping array.

    Natural language breakdown:
    1. Each interval is a pair (start, end) with start ≤ end.
    2. The input array `intervals` is sorted by start in nondecreasing order.
    3. The input array has no overlaps: every interval ends strictly before the next begins.
    4. A new interval `newInterval` is given and also satisfies start ≤ end.
    5. We must insert `newInterval` and merge any overlapping/touching intervals so the result has no overlaps.
    6. The result must remain sorted by start.
    7. Coverage semantics: the set of integer points covered by the result equals the union of coverage
       of the input intervals and the new interval.
    8. The result must be canonical: sorted, non-overlapping, and each interval has start ≤ end.
       (This uniqueness ensures the output is determined by the covered set.)
    Your algorithm should run in **O(n)** time and **O(n)** extra space.
-/

section Specs
-- Basic interval type: (start, end)
abbrev Interval := Int × Int

-- Accessors
abbrev istart (i : Interval) : Int := i.1
abbrev iend (i : Interval) : Int := i.2

-- Well-formed interval
@[simp] def wfInterval (i : Interval) : Prop := istart i ≤ iend i

-- Array is sorted by start (nondecreasing)
def sortedByStart (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → istart a[i]! ≤ istart a[i+1]!

-- No overlaps between consecutive intervals in array
-- We use strict separation: end < next.start.
-- This matches the problem statement “non-overlapping” for closed intervals.
def noOverlapConsecutive (a : Array Interval) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → iend a[i]! < istart a[i+1]!

-- Every interval in array is well-formed

def allWf (a : Array Interval) : Prop :=
  ∀ (i : Nat), i < a.size → wfInterval a[i]!

-- Membership of a point in a closed interval
@[simp] def memInterval (x : Int) (i : Interval) : Prop :=
  istart i ≤ x ∧ x ≤ iend i

-- Point coverage of an interval array
-- (Using an existential over indices is simple and decidable-friendly in SMT contexts.)
def coveredBy (x : Int) (a : Array Interval) : Prop :=
  ∃ (i : Nat), i < a.size ∧ memInterval x a[i]!

-- Canonical form for the output: sorted, no overlaps, and well-formed

def canonical (a : Array Interval) : Prop :=
  sortedByStart a ∧ noOverlapConsecutive a ∧ allWf a

-- Preconditions

def precondition (intervals : Array Interval) (newInterval : Interval) : Prop :=
  canonical intervals ∧ wfInterval newInterval

-- Postconditions

def postcondition (intervals : Array Interval) (newInterval : Interval) (result : Array Interval) : Prop :=
  canonical result ∧
  -- Coverage equivalence: result covers exactly the union of old coverage and new interval coverage
  (∀ (x : Int), coveredBy x result ↔ coveredBy x intervals ∨ memInterval x newInterval) ∧
  -- Minimality/canonicity already implies uniqueness for a given covered set; we add a simple anti-fragmentation:
  -- no two consecutive result intervals can be merged (i.e., they are strictly separated).
  (∀ (i : Nat), i + 1 < result.size → iend result[i]! < istart result[i+1]!)
end Specs

section Impl
method InsertInterval (intervals : Array Interval) (newInterval : Interval)
  return (result : Array Interval)
  require precondition intervals newInterval
  ensures postcondition intervals newInterval result
  do
    pure #[]

end Impl

section TestCases
-- Test case 1: Example 1
-- intervals = [[1,3],[6,9]], newInterval = [2,5] => [[1,5],[6,9]]
def test1_intervals : Array Interval := #[(1, 3), (6, 9)]
def test1_newInterval : Interval := (2, 5)
def test1_Expected : Array Interval := #[(1, 5), (6, 9)]

-- Test case 2: Example 2
-- intervals = [[1,2],[3,5],[6,7],[8,10],[12,16]], newInterval = [4,8] => [[1,2],[3,10],[12,16]]
def test2_intervals : Array Interval := #[(1, 2), (3, 5), (6, 7), (8, 10), (12, 16)]
def test2_newInterval : Interval := (4, 8)
def test2_Expected : Array Interval := #[(1, 2), (3, 10), (12, 16)]

-- Test case 3: Empty intervals

def test3_intervals : Array Interval := #[]
def test3_newInterval : Interval := (2, 3)
def test3_Expected : Array Interval := #[(2, 3)]

-- Test case 4: New interval strictly before all, no overlap

def test4_intervals : Array Interval := #[(5, 7), (10, 12)]
def test4_newInterval : Interval := (1, 3)
def test4_Expected : Array Interval := #[(1, 3), (5, 7), (10, 12)]

-- Test case 5: New interval strictly after all, no overlap

def test5_intervals : Array Interval := #[(1, 2), (4, 5)]
def test5_newInterval : Interval := (7, 9)
def test5_Expected : Array Interval := #[(1, 2), (4, 5), (7, 9)]

-- Test case 6: New interval contained inside an existing interval (no change)

def test6_intervals : Array Interval := #[(1, 10)]
def test6_newInterval : Interval := (3, 4)
def test6_Expected : Array Interval := #[(1, 10)]

-- Test case 7: New interval overlaps multiple and merges all into one

def test7_intervals : Array Interval := #[(1, 2), (4, 6), (8, 9)]
def test7_newInterval : Interval := (2, 8)
def test7_Expected : Array Interval := #[(1, 9)]

-- Test case 8: Negative coordinates and merging across zero

def test8_intervals : Array Interval := #[(-10, -5), (-3, -1), (2, 4)]
def test8_newInterval : Interval := (-6, 3)
def test8_Expected : Array Interval := #[(-10, 4)]

-- Test case 9: Singleton intervals array where insertion creates a second interval

def test9_intervals : Array Interval := #[(0, 0)]
def test9_newInterval : Interval := (2, 2)
def test9_Expected : Array Interval := #[(0, 0), (2, 2)]
end TestCases
