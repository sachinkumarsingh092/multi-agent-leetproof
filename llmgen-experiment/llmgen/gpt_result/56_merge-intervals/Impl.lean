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
    let n := intervals.size
    if n = 0 then
      return #[]
    else
      -- current interval being merged
      let mut curStart : Int := istart intervals[0]!
      let mut curEnd : Int := iend intervals[0]!
      let mut out : Array Interval := #[]
      let mut i : Nat := 1

      while i < n
        -- i stays within bounds, and n is the fixed array size.
        invariant "inv_bounds" (i ≤ n ∧ n = intervals.size)
        -- i starts at 1, so intervals[0] is the initial current interval.
        invariant "inv_i_pos" (1 ≤ i)
        -- Current interval is always valid.
        invariant "inv_cur_valid" (curStart ≤ curEnd)
        -- Already-flushed output intervals are valid, sorted, and strictly separated.
        invariant "inv_out_valid" (AllValid out)
        invariant "inv_out_sorted" (NondecreasingStarts out)
        invariant "inv_out_sep" (StrictlyNonOverlapping out)
        -- The last flushed interval (if any) ends strictly before the current interval starts.
        invariant "inv_out_before_cur" (out.size = 0 ∨ iend out[out.size - 1]! < curStart)
        -- Semantic invariant: flushed intervals plus current represent exactly the covered points
        -- of the already-processed prefix intervals[0..i).
        invariant "inv_cov_prefix" (∀ (x : Int), CoveredBy x (out.push (curStart, curEnd)) ↔ CoveredBy x (intervals.extract 0 i))
        decreasing n - i
      do
        let s : Int := istart intervals[i]!
        let e : Int := iend intervals[i]!
        if s <= curEnd then
          -- overlap/touch: extend current end if needed
          if curEnd < e then
            curEnd := e
          else
            pure ()
        else
          -- separated: flush current, start new
          out := out.push (curStart, curEnd)
          curStart := s
          curEnd := e
        i := i + 1

      -- flush last interval
      out := out.push (curStart, curEnd)
      return out
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

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (intervals : Array Interval)
    (require_1 : precondition intervals)
    (if_neg : ¬intervals.size = OfNat.ofNat 0)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (out : Array Interval)
    (invariant_inv_bounds : i ≤ intervals.size)
    (invariant_inv_i_pos : OfNat.ofNat 1 ≤ i)
    (invariant_inv_cur_valid : curStart ≤ curEnd)
    (invariant_inv_out_valid : AllValid out)
    (invariant_inv_out_sorted : NondecreasingStarts out)
    (invariant_inv_out_sep : StrictlyNonOverlapping out)
    (invariant_inv_out_before_cur : out.size = OfNat.ofNat 0 ∨ iend out[out.size - OfNat.ofNat 1]! < curStart)
    (invariant_inv_cov_prefix : ∀ (x : ℤ), CoveredBy x (out.push (curStart, curEnd)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) i))
    (if_pos : i < intervals.size)
    (if_pos_1 : istart intervals[i]! ≤ curEnd)
    (if_pos_2 : curEnd < iend intervals[i]!)
    : ∀ (x : ℤ), CoveredBy x (out.push (curStart, iend intervals[i]!)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    sorry

lemma Array.getBang_eq_getElem' {α} [Inhabited α] (xs : Array α) (i : Nat) (h : i < xs.size) :
    xs[i]! = xs[i]'h := by
  simp [Array.get!, Array.getElem?_eq_getElem, h]

theorem goal_1
    (intervals : Array Interval)
    (require_1 : precondition intervals)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (out : Array Interval)
    (invariant_inv_bounds : i ≤ intervals.size)
    (invariant_inv_cur_valid : curStart ≤ curEnd)
    (invariant_inv_cov_prefix : ∀ (x : ℤ), CoveredBy x (out.push (curStart, curEnd)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) i))
    (if_pos : i < intervals.size)
    (if_neg_1 : ¬curEnd < iend intervals[i]!)
    : ∀ (x : ℤ), CoveredBy x (out.push (curStart, curEnd)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  classical

  have hLex : LexSortedIntervals intervals := require_1.2

  have hsize_i : (intervals.extract 0 i).size = i := by
    have hi : i ≤ intervals.size := invariant_inv_bounds
    simp [Array.size_extract, hi, Nat.min_eq_left]
  have hsize_succ : (intervals.extract 0 (i+1)).size = i+1 := by
    have hi : i + 1 ≤ intervals.size := Nat.succ_le_of_lt if_pos
    simp [Array.size_extract, hi, Nat.min_eq_left]

  -- helper: element of extract(0,stop) at j (as `!`) is the original element at j
  have get_extract0 (stop j : Nat) (hstop : stop ≤ intervals.size) (hj : j < stop) :
      (intervals.extract 0 stop)[j]! = intervals[j]! := by
    have hsize : (intervals.extract 0 stop).size = stop := by
      simp [Array.size_extract, hstop, Nat.min_eq_left]
    have hj' : j < (intervals.extract 0 stop).size := by
      simpa [hsize] using hj
    have hjSize : j < intervals.size := lt_of_lt_of_le hj hstop

    -- `get!` = `getElem` in bounds
    have hbangL : (intervals.extract 0 stop)[j]! = (intervals.extract 0 stop)[j]'hj' :=
      Array.getBang_eq_getElem' (xs := intervals.extract 0 stop) (i := j) hj'
    have hbangR : intervals[j]! = intervals[j]'hjSize :=
      Array.getBang_eq_getElem' (xs := intervals) (i := j) hjSize

    -- compute the extracted element
    have hget : (intervals.extract 0 stop)[j]'hj' =
        intervals[0 + j]'(Array.getElem_extract_aux (xs := intervals) (start := 0) (stop := stop) (i := j) hj') := by
      -- `getElem_extract` already uses the same bound proof `hj'` on the LHS
      simpa using (Array.getElem_extract (xs := intervals) (start := 0) (stop := stop) (i := j) hj')

    -- align the RHS proof with `hjSize`
    have hjAux0 : 0 + j < intervals.size :=
      Array.getElem_extract_aux (xs := intervals) (start := 0) (stop := stop) (i := j) hj'
    have hjAux : j < intervals.size := by
      simpa using hjAux0
    have hproof : hjAux = hjSize := by
      apply Subsingleton.elim

    calc
      (intervals.extract 0 stop)[j]! = (intervals.extract 0 stop)[j]'hj' := hbangL
      _ = intervals[j]'hjAux := by
            simpa [hget, Nat.zero_add]
      _ = intervals[j]'hjSize := by
            simpa [hproof]
      _ = intervals[j]! := by
            simpa [hbangR]

  -- helper: adjacent-start monotonicity from LexSortedIntervals
  have start_le_succ (n : Nat) (hn : n + 1 < intervals.size) :
      istart intervals[n]! ≤ istart intervals[n+1]! := by
    have h := hLex n hn
    rcases h with hlt | heq | heq
    · exact le_of_lt hlt
    · exact le_of_eq heq.1
    · exact le_of_eq heq.1

  -- helper: nondecreasing starts in the input array
  have start_mono : ∀ {k m : Nat}, k < m → m < intervals.size → istart intervals[k]! ≤ istart intervals[m]! := by
    intro k m hkm hm
    induction m generalizing k with
    | zero => cases (Nat.not_lt_zero _ hkm)
    | succ m ih =>
        have hm' : m < intervals.size := Nat.lt_of_succ_lt hm
        have hstep : istart intervals[m]! ≤ istart intervals[m+1]! := start_le_succ m hm
        have hk_le : k ≤ m := Nat.le_of_lt_succ hkm
        rcases lt_or_eq_of_le hk_le with hklt | hkeq
        · exact le_trans (ih hklt hm') hstep
        · subst hkeq
          exact hstep

  have hend : iend intervals[i]! ≤ curEnd := by
    exact le_of_not_gt (a := iend intervals[i]!) (b := curEnd) (by simpa using if_neg_1)

  -- Key claim: every point in the new interval is already covered by the old prefix.
  have new_interval_covered_by_prefix : ∀ (x : ℤ), InInterval x intervals[i]! → CoveredBy x (intervals.extract 0 i) := by
    intro x hxI
    -- show curEnd is covered by the prefix, then pick an interval from the prefix that contains curEnd
    have hcurEnd_out : CoveredBy curEnd (out.push (curStart, curEnd)) := by
      refine ⟨out.size, ?_, ?_⟩
      · simpa using (Nat.lt_succ_self out.size)
      · -- last element of push is the pushed interval
        have hlt : out.size < (out.push (curStart, curEnd)).size := by
          simpa using (Nat.lt_succ_self out.size)
        have hlast : (out.push (curStart, curEnd))[out.size]! = (curStart, curEnd) := by
          calc
            (out.push (curStart, curEnd))[out.size]! = (out.push (curStart, curEnd))[out.size]'hlt :=
              Array.getBang_eq_getElem' (xs := out.push (curStart, curEnd)) (i := out.size) hlt
            _ = (curStart, curEnd) := by
              simpa using (Array.getElem_push_eq (xs := out) (x := (curStart, curEnd)))
        have : InInterval curEnd (curStart, curEnd) := by
          simp [InInterval, istart, iend, invariant_inv_cur_valid]
        simpa [hlast] using this

    have hcurEnd_pref : CoveredBy curEnd (intervals.extract 0 i) := (invariant_inv_cov_prefix curEnd).1 hcurEnd_out

    rcases hcurEnd_pref with ⟨k, hk, hkI⟩
    have hklt : k < i := by
      simpa [hsize_i] using hk

    have hk_elem : (intervals.extract 0 i)[k]! = intervals[k]! :=
      get_extract0 i k invariant_inv_bounds hklt
    have hkI' : InInterval curEnd (intervals[k]!) := by
      simpa [hk_elem] using hkI

    have hstartki : istart intervals[k]! ≤ istart intervals[i]! := start_mono hklt if_pos

    rcases hxI with ⟨hsx, hxe⟩
    have hx_le_curEnd : x ≤ curEnd := le_trans hxe hend
    have hcurEnd_le_endk : curEnd ≤ iend intervals[k]! := hkI'.2
    have hx_endk : x ≤ iend intervals[k]! := le_trans hx_le_curEnd hcurEnd_le_endk
    have hx_startk : istart intervals[k]! ≤ x := le_trans hstartki hsx

    have hxI_k : InInterval x (intervals[k]!) := ⟨hx_startk, hx_endk⟩
    refine ⟨k, hk, ?_⟩
    simpa [hk_elem] using hxI_k

  intro x
  constructor
  · intro hx
    have hx' : CoveredBy x (intervals.extract 0 i) := (invariant_inv_cov_prefix x).1 hx
    rcases hx' with ⟨j, hj, hjI⟩
    have hjlt : j < i := by
      simpa [hsize_i] using hj
    have hj' : j < i + 1 := Nat.lt_succ_of_lt hjlt
    have hj_elem_i : (intervals.extract 0 i)[j]! = intervals[j]! :=
      get_extract0 i j invariant_inv_bounds hjlt
    have hj_elem_succ : (intervals.extract 0 (i+1))[j]! = intervals[j]! :=
      get_extract0 (i+1) j (Nat.succ_le_of_lt if_pos) hj'
    have hjI' : InInterval x (intervals[j]!) := by
      simpa [hj_elem_i] using hjI
    have hjI_succ : InInterval x (intervals.extract 0 (i+1))[j]! := by
      simpa [hj_elem_succ] using hjI'
    refine ⟨j, ?_, hjI_succ⟩
    simpa [hsize_succ] using hj'

  · intro hx
    rcases hx with ⟨j, hj, hjI⟩
    have hj' : j < i + 1 := by
      simpa [hsize_succ] using hj
    have hjle : j ≤ i := Nat.le_of_lt_succ hj'
    rcases lt_or_eq_of_le hjle with hjlt | hjeq
    · have hj0 : j < (intervals.extract 0 i).size := by
        have : j < i := hjlt
        simpa [hsize_i] using this
      have hj_elem_succ : (intervals.extract 0 (i+1))[j]! = intervals[j]! :=
        get_extract0 (i+1) j (Nat.succ_le_of_lt if_pos) hj'
      have hj_elem_i : (intervals.extract 0 i)[j]! = intervals[j]! :=
        get_extract0 i j invariant_inv_bounds hjlt
      have hjI' : InInterval x (intervals[j]!) := by
        simpa [hj_elem_succ] using hjI
      have hjI_i : InInterval x (intervals.extract 0 i)[j]! := by
        simpa [hj_elem_i] using hjI'
      have : CoveredBy x (intervals.extract 0 i) := ⟨j, hj0, hjI_i⟩
      exact (invariant_inv_cov_prefix x).2 this
    · -- j = i
      cases hjeq
      have hi_lt : i < i + 1 := Nat.lt_succ_self i
      have hi_elem_succ : (intervals.extract 0 (i+1))[i]! = intervals[i]! :=
        get_extract0 (i+1) i (Nat.succ_le_of_lt if_pos) hi_lt
      have hxI : InInterval x (intervals[i]!) := by
        simpa [hi_elem_succ] using hjI
      have hxPref : CoveredBy x (intervals.extract 0 i) := new_interval_covered_by_prefix x hxI
      exact (invariant_inv_cov_prefix x).2 hxPref

theorem goal_2
    (intervals : Array Interval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (out : Array Interval)
    (invariant_inv_cov_prefix : ∀ (x : ℤ), CoveredBy x (out.push (curStart, curEnd)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) i))
    (if_pos : i < intervals.size)
    : ∀ (x : ℤ), CoveredBy x ((out.push (curStart, curEnd)).push (istart intervals[i]!, iend intervals[i]!)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  classical

  -- Turn `getElem!` into `getElem` using an in-bounds proof.
  have getBang_eq_getElem (xs : Array Interval) (k : Nat) (hk : k < xs.size) :
      xs[k]! = xs[k]'hk := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, hk]

  -- Generic lemma: coverage after pushing an interval.
  have coveredBy_push (x : Int) (a : Array Interval) (iv : Interval) :
      CoveredBy x (a.push iv) ↔ CoveredBy x a ∨ InInterval x iv := by
    unfold CoveredBy
    constructor
    · rintro ⟨j, hj, hx⟩
      have hx' : InInterval x ((a.push iv)[j]'hj) := by
        simpa [getBang_eq_getElem (xs := a.push iv) (k := j) hj] using hx
      have hget := (Array.getElem_push (xs := a) (x := iv) (i := j) hj)
      have hx'' : InInterval x (if h : j < a.size then a[j]'h else iv) := by
        simpa [hget] using hx'
      by_cases hja : j < a.size
      · left
        refine ⟨j, hja, ?_⟩
        have : InInterval x (a[j]'hja) := by
          simpa [hja] using hx''
        simpa [getBang_eq_getElem (xs := a) (k := j) hja] using this
      · right
        simpa [hja] using hx''
    · rintro (hcov | hin)
      · rcases hcov with ⟨j, hj, hx⟩
        refine ⟨j, ?_, ?_⟩
        · simpa [Array.size_push] using Nat.lt_succ_of_lt hj
        · have hj' : j < (a.push iv).size := by
            simpa [Array.size_push] using Nat.lt_succ_of_lt hj
          have hx' : InInterval x (a[j]'hj) := by
            simpa [getBang_eq_getElem (xs := a) (k := j) hj] using hx
          have hget := (Array.getElem_push (xs := a) (x := iv) (i := j) hj')
          have : InInterval x ((a.push iv)[j]'hj') := by
            simpa [hget, dif_pos hj] using hx'
          simpa [getBang_eq_getElem (xs := a.push iv) (k := j) hj'] using this
      · refine ⟨a.size, ?_, ?_⟩
        · simpa [Array.size_push] using Nat.lt_succ_self a.size
        · have hj' : a.size < (a.push iv).size := by
            simpa [Array.size_push] using Nat.lt_succ_self a.size
          have hget := (Array.getElem_push (xs := a) (x := iv) (i := a.size) hj')
          have : InInterval x ((a.push iv)[a.size]'hj') := by
            simpa [hget] using hin
          simpa [getBang_eq_getElem (xs := a.push iv) (k := a.size) hj'] using this

  intro x

  let ivInput : Interval := intervals[i]'if_pos
  have hbang : intervals[i]! = ivInput := by
    simpa [ivInput] using (getBang_eq_getElem (xs := intervals) (k := i) if_pos)

  have hextract : intervals.extract 0 (i + 1) = (intervals.extract 0 i).push ivInput := by
    have h := (@Array.push_extract_getElem Interval intervals 0 i if_pos)
    simpa [ivInput, Nat.min_eq_left (Nat.zero_le i)] using h.symm

  have hininterval : InInterval x (istart intervals[i]!, iend intervals[i]!) ↔ InInterval x ivInput := by
    -- rewrite `intervals[i]!` to `ivInput` and unfold `InInterval`.
    simp [InInterval, istart, iend, hbang, ivInput]

  -- Rewrite the disjunction using the coverage invariant.
  have hor :
      (CoveredBy x (out.push (curStart, curEnd)) ∨ InInterval x (istart intervals[i]!, iend intervals[i]!))
        ↔ (CoveredBy x (intervals.extract 0 i) ∨ InInterval x (istart intervals[i]!, iend intervals[i]!)) := by
    constructor
    · intro h
      cases h with
      | inl hcov => exact Or.inl ((invariant_inv_cov_prefix x).1 hcov)
      | inr hin  => exact Or.inr hin
    · intro h
      cases h with
      | inl hcov => exact Or.inl ((invariant_inv_cov_prefix x).2 hcov)
      | inr hin  => exact Or.inr hin

  calc
    CoveredBy x ((out.push (curStart, curEnd)).push (istart intervals[i]!, iend intervals[i]!))
        ↔ CoveredBy x (out.push (curStart, curEnd)) ∨ InInterval x (istart intervals[i]!, iend intervals[i]!) := by
          simpa using
            (coveredBy_push x (out.push (curStart, curEnd)) (istart intervals[i]!, iend intervals[i]!))
    _ ↔ CoveredBy x (intervals.extract 0 i) ∨ InInterval x (istart intervals[i]!, iend intervals[i]!) := by
          simpa using hor
    _ ↔ CoveredBy x (intervals.extract 0 i) ∨ InInterval x ivInput := by
          -- only the right disjunct changes
          constructor
          · intro h
            cases h with
            | inl hcov => exact Or.inl hcov
            | inr hin  => exact Or.inr ((hininterval).1 hin)
          · intro h
            cases h with
            | inl hcov => exact Or.inl hcov
            | inr hin  => exact Or.inr ((hininterval).2 hin)
    _ ↔ CoveredBy x ((intervals.extract 0 i).push ivInput) := by
          simpa using (coveredBy_push x (intervals.extract 0 i) ivInput).symm
    _ ↔ CoveredBy x (intervals.extract 0 (i + 1)) := by
          simpa [hextract]
    _ ↔ CoveredBy x (intervals.extract 0 (i + OfNat.ofNat 1)) := by
          simp

theorem goal_3
    (intervals : Array Interval)
    (require_1 : precondition intervals)
    (if_neg : ¬intervals.size = OfNat.ofNat 0)
    : ∀ (x : ℤ), CoveredBy x (#[].push (istart intervals[OfNat.ofNat 0]!, iend intervals[OfNat.ofNat 0]!)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) := by
    intros; expose_names; try simp_all; try grind



theorem goal_4
    (intervals : Array Interval)
    (require_1 : precondition intervals)
    (if_neg : ¬intervals.size = OfNat.ofNat 0)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (out_1 : Array Interval)
    (invariant_inv_cur_valid : i_2 ≤ i_1)
    (invariant_inv_bounds : i_3 ≤ intervals.size)
    (invariant_inv_i_pos : OfNat.ofNat 1 ≤ i_3)
    (done_1 : ¬i_3 < intervals.size)
    (invariant_inv_out_valid : AllValid out_1)
    (invariant_inv_out_sorted : NondecreasingStarts out_1)
    (invariant_inv_out_sep : StrictlyNonOverlapping out_1)
    (invariant_inv_out_before_cur : out_1.size = OfNat.ofNat 0 ∨ iend out_1[out_1.size - OfNat.ofNat 1]! < i_2)
    (invariant_inv_cov_prefix : ∀ (x : ℤ), CoveredBy x (out_1.push (i_2, i_1)) ↔ CoveredBy x (intervals.extract (OfNat.ofNat 0) i_3))
    : postcondition intervals (out_1.push (i_2, i_1)) := by
    sorry



prove_correct MergeIntervals by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 intervals require_1 if_neg curEnd curStart i out invariant_inv_bounds invariant_inv_i_pos invariant_inv_cur_valid invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_sep invariant_inv_out_before_cur invariant_inv_cov_prefix if_pos if_pos_1 if_pos_2)
  exact (goal_1 intervals require_1 curEnd curStart i out invariant_inv_bounds invariant_inv_cur_valid invariant_inv_cov_prefix if_pos if_neg_1)
  exact (goal_2 intervals curEnd curStart i out invariant_inv_cov_prefix if_pos)
  exact (goal_3 intervals require_1 if_neg)
  exact (goal_4 intervals require_1 if_neg i_1 i_2 i_3 out_1 invariant_inv_cur_valid invariant_inv_bounds invariant_inv_i_pos done_1 invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_sep invariant_inv_out_before_cur invariant_inv_cov_prefix)
end Proof
