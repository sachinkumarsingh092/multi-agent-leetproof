/- This file type checks in Lean 4.28 -/

import Lean

import Mathlib.Tactic

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

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
def implementation (intervals : Array Interval) : Array Interval :=
  if intervals.size == 0 then #[]
  else
    let first := intervals[0]!
    let init : Array Interval × Interval := (#[], first)
    let (result, last) := intervals.foldl (fun (acc : Array Interval × Interval) (iv : Interval) =>
      let (merged, current) := acc
      if iv.1 ≤ current.2 then
        -- Overlapping or touching: extend current interval
        (merged, (current.1, max current.2 iv.2))
      else
        -- No overlap: push current and start new
        (merged.push current, iv)
    ) init 1
    result.push last
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

section Proof

theorem correctness_goal_1_0 (intervals : Array Interval) (h_valid : AllValid intervals) (h_sorted : LexSortedIntervals intervals) (h_allvalid : AllValid (implementation intervals)) (h_empty : ¬(intervals.size == 0) = true) (h_sz : 0 < intervals.size) (h_nondec_starts_input : ∀ (i : ℕ), i + 1 < intervals.size → istart intervals[i]! ≤ istart intervals[i + 1]!) : NondecreasingStarts
    (Array.foldl
        (fun acc iv =>
          Prod.casesOn acc fun fst snd =>
            (fun merged current =>
                if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
              fst snd)
        (#[], intervals[0]!) intervals 1).1 ∧
  (0 <
      (Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).1.size →
    istart
        (Array.foldl
              (fun acc iv =>
                Prod.casesOn acc fun fst snd =>
                  (fun merged current =>
                      if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                    fst snd)
              (#[], intervals[0]!) intervals
              1).1[(Array.foldl
                  (fun acc iv =>
                    Prod.casesOn acc fun fst snd =>
                      (fun merged current =>
                          if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2)
                          else (merged.push current, iv))
                        fst snd)
                  (#[], intervals[0]!) intervals 1).1.size -
            1]! ≤
      istart
        (Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).2) := by
    sorry

theorem correctness_goal_2 (intervals : Array Interval) (h_valid : AllValid intervals) (h_sorted : LexSortedIntervals intervals) (h_allvalid : AllValid (implementation intervals)) (h_nondec : NondecreasingStarts (implementation intervals)) : StrictlyNonOverlapping (implementation intervals) := by
    sorry

theorem correctness_goal_3 (intervals : Array Interval) (h_valid : AllValid intervals) (h_sorted : LexSortedIntervals intervals) (h_allvalid : AllValid (implementation intervals)) (h_nondec : NondecreasingStarts (implementation intervals)) (h_nonoverlap : StrictlyNonOverlapping (implementation intervals)) : ∀ (x : ℤ), CoveredBy x (implementation intervals) ↔ CoveredBy x intervals := by
    sorry

/-
PROVIDED SOLUTION
This follows directly from h_coverage and h_allvalid. For any result interval result[i] with i < result.size:
- result[i] is valid so istart result[i]! ≤ iend result[i]!
- istart result[i]! is InInterval of result[i]! (by le_refl and validity), so CoveredBy (istart result[i]!) result, so by h_coverage, CoveredBy (istart result[i]!) intervals
- Similarly iend result[i]! is InInterval result[i]!, so CoveredBy (iend result[i]!) result, hence CoveredBy (iend result[i]!) intervals
- For any x with istart result[i]! ≤ x ≤ x ≤ iend result[i]!, x is InInterval result[i]!, so CoveredBy x result, hence CoveredBy x intervals by h_coverage
-/
theorem correctness_goal_4 (intervals : Array Interval) (h_valid : AllValid intervals) (h_sorted : LexSortedIntervals intervals) (h_allvalid : AllValid (implementation intervals)) (h_nondec : NondecreasingStarts (implementation intervals)) (h_nonoverlap : StrictlyNonOverlapping (implementation intervals)) (h_coverage : ∀ (x : ℤ), CoveredBy x (implementation intervals) ↔ CoveredBy x intervals) : ∀ i < (implementation intervals).size, IntervalIsTight intervals (implementation intervals)[i]! := by
    intros i hi;
    refine' ⟨ _, _, _ ⟩;
    · refine' h_coverage _ |>.1 _;
      use i;
      exact ⟨ hi, le_rfl, h_allvalid _ hi ⟩;
    · refine' h_coverage _ |>.1 _;
      use i, hi;
      exact ⟨ h_allvalid i hi, le_rfl ⟩;
    · intro x hx
      have h_covered : CoveredBy x (implementation intervals) := by
        exact ⟨ i, hi, hx ⟩
      exact h_coverage x |>.1 h_covered

end Proof
