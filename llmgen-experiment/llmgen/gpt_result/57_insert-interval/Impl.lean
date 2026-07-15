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
    -- Standard O(n) scan/merge approach.
    let mut res : Array Interval := #[]

    let mut curStart : Int := istart newInterval
    let mut curEnd : Int := iend newInterval

    let mut i : Nat := 0
    let mut inserted : Bool := false

    while i < intervals.size
      -- Invariant: index stays within bounds.
      invariant "inv_i_bounds" (i ≤ intervals.size)
      -- Invariant: the pending merged interval is always well-formed.
      invariant "inv_pending_wf" (curStart ≤ curEnd)
      -- Invariant: accumulated output so far is canonical.
      invariant "inv_res_canonical" (canonical res)
      -- Invariant: if res is nonempty, its last interval is strictly before the next input interval
      -- (needed to preserve canonicality when pushing intervals[i]!).
      invariant "inv_last_before_next_input"
        (i < intervals.size → (res.size = 0 ∨ iend res[res.size - 1]! < istart intervals[i]!))
      -- Invariant: before insertion, everything already in res lies strictly before the pending interval.
      invariant "inv_last_before_pending"
        (inserted = false → (res.size = 0 ∨ iend res[res.size - 1]! < curStart))
      -- Invariant: coverage of processed prefix + pending interval matches coverage of original processed prefix + newInterval.
      invariant "inv_coverage" (∀ x : Int,
        (coveredBy x res ∨ (inserted = false ∧ memInterval x (curStart, curEnd))) ↔
        (coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval))
      -- Invariant: once inserted, the pending interval has been appended into res.
      invariant "inv_inserted_has_pending" (inserted = true → (∃ j : Nat, j < res.size ∧ res[j]! = (curStart, curEnd)))
      decreasing intervals.size - i
    do
      let iv := intervals[i]!
      let s := istart iv
      let e := iend iv

      if inserted then
        -- After insertion, just append remaining original intervals.
        res := res.push iv
        i := i + 1
      else
        -- Not inserted yet: decide relation between current interval and current (possibly merged) new interval.
        if e < curStart then
          -- Current interval strictly before new interval: keep it.
          res := res.push iv
          i := i + 1
        else
          if curEnd < s then
            -- New interval strictly before current interval: insert it now, then keep current.
            res := res.push (curStart, curEnd)
            inserted := true
            res := res.push iv
            i := i + 1
          else
            -- Overlapping/touching: merge into current interval.
            if s < curStart then
              curStart := s
            if curEnd < e then
              curEnd := e
            i := i + 1

    if inserted = false then
      res := res.push (curStart, curEnd)

    return res
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

section Assertions
-- Test case 1

#assert_same_evaluation #[((InsertInterval test1_intervals test1_newInterval).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((InsertInterval test2_intervals test2_newInterval).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((InsertInterval test3_intervals test3_newInterval).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((InsertInterval test4_intervals test4_newInterval).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((InsertInterval test5_intervals test5_newInterval).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((InsertInterval test6_intervals test6_newInterval).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((InsertInterval test7_intervals test7_newInterval).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((InsertInterval test8_intervals test8_newInterval).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((InsertInterval test9_intervals test9_newInterval).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- velvet_plausible_test InsertInterval (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

lemma Array.getElem!_eq_getElem_of_lt {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  -- `getElem!` is `getD`; `getD` returns the in-bounds element.
  simp [Array.getElem!_eq_getD, Array.getD, h]


lemma coveredBy_push_iff (x : Int) (a : Array Interval) (iv : Interval) :
  coveredBy x (a.push iv) ↔ coveredBy x a ∨ memInterval x iv := by
  classical
  unfold coveredBy
  constructor
  · rintro ⟨k, hk, hx⟩
    have hk' : k < a.size + 1 := by
      simpa [Array.size_push, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hk
    by_cases hka : k < a.size
    · left
      refine ⟨k, hka, ?_⟩
      have hkpush : k < (a.push iv).size := by
        simpa [Array.size_push, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.lt_trans hka (Nat.lt_succ_self a.size))
      have hx' : memInterval x ((a.push iv)[k]) := by
        simpa [Array.getElem!_eq_getElem_of_lt (a := a.push iv) (i := k) hkpush] using hx
      have hpush_get : (a.push iv)[k] = a[k] := by
        simpa [Array.getElem_push, hkpush, hka] using
          (Array.getElem_push (xs := a) (x := iv) (i := k) hkpush)
      have : memInterval x (a[k]) := by simpa [hpush_get] using hx'
      simpa [Array.getElem!_eq_getElem_of_lt (a := a) (i := k) hka] using this
    · right
      have hkEq : k = a.size := Nat.eq_of_lt_succ_of_not_lt hk' hka
      subst hkEq
      have hkpush : a.size < (a.push iv).size := by
        simpa [Array.size_push]
      have hx' : memInterval x ((a.push iv)[a.size]) := by
        simpa [Array.getElem!_eq_getElem_of_lt (a := a.push iv) (i := a.size) hkpush] using hx
      have hpush_get : (a.push iv)[a.size] = iv := by
        simpa [Array.getElem_push, hkpush, Nat.lt_irrefl] using
          (Array.getElem_push (xs := a) (x := iv) (i := a.size) hkpush)
      simpa [hpush_get] using hx'
  · intro h
    rcases h with h | h
    · rcases h with ⟨k, hk, hx⟩
      have hkpush : k < (a.push iv).size := by
        have : k < a.size + 1 := Nat.lt_trans hk (Nat.lt_succ_self a.size)
        simpa [Array.size_push, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      refine ⟨k, hkpush, ?_⟩
      have hpush_get : (a.push iv)[k] = a[k] := by
        simpa [Array.getElem_push, hkpush, hk] using
          (Array.getElem_push (xs := a) (x := iv) (i := k) hkpush)
      have : memInterval x (a[k]) := by
        simpa [Array.getElem!_eq_getElem_of_lt (a := a) (i := k) hk] using hx
      have : memInterval x ((a.push iv)[k]) := by simpa [hpush_get] using this
      simpa [Array.getElem!_eq_getElem_of_lt (a := a.push iv) (i := k) hkpush] using this
    · have hkpush : a.size < (a.push iv).size := by
        simpa [Array.size_push]
      refine ⟨a.size, hkpush, ?_⟩
      have hpush_get : (a.push iv)[a.size] = iv := by
        simpa [Array.getElem_push, hkpush, Nat.lt_irrefl] using
          (Array.getElem_push (xs := a) (x := iv) (i := a.size) hkpush)
      have : memInterval x ((a.push iv)[a.size]) := by simpa [hpush_get] using h
      simpa [Array.getElem!_eq_getElem_of_lt (a := a.push iv) (i := a.size) hkpush] using this

theorem goal_0
    (intervals : Array Interval)
    (newInterval : Interval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (res : Array Interval)
    (if_pos : i < intervals.size)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ true = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    : ∀ (x : ℤ), coveredBy x (res.push intervals[i]!) ∨ true = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
  classical
  intro x

  have hcov : coveredBy x res ↔ coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval := by
    simpa using (invariant_inv_coverage x)

  have hi : intervals[i]! = intervals[i] := by
    simpa using (Array.getElem!_eq_getElem_of_lt intervals i if_pos)

  have hextract : intervals.extract 0 (i + 1) = (intervals.extract 0 i).push intervals[i] := by
    simpa using
      (Array.extract_succ_right (i := (0 : Nat)) (j := i) (w := Nat.succ_pos i) (h := if_pos) :
        intervals.extract 0 (i + 1) = (intervals.extract 0 i).push intervals[i])

  constructor
  · intro h
    -- extract the meaningful disjunct (the other one is impossible)
    have hpush : coveredBy x (res.push intervals[i]!) := by
      rcases h with hpush | hfalse
      · exact hpush
      · cases hfalse.1

    have h1 : coveredBy x res ∨ memInterval x intervals[i]! :=
      (coveredBy_push_iff x res (intervals[i]!)).1 hpush

    -- prove the RHS
    rcases h1 with hres | hiv
    · have h2 : coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval := hcov.mp hres
      rcases h2 with hpre | hnew
      · -- show covered by extract 0 (i+1)
        have hprePush : coveredBy x ((intervals.extract 0 i).push intervals[i]) :=
          (coveredBy_push_iff x (intervals.extract 0 i) intervals[i]).2 (Or.inl hpre)
        have : coveredBy x (intervals.extract 0 (i + 1)) := by
          -- rewrite goal using hextract
          -- (goal becomes coverage of the pushed prefix)
          rw [hextract]
          exact hprePush
        exact Or.inl this
      · exact Or.inr hnew
    · -- in the pushed interval
      have hiv' : memInterval x intervals[i] := by simpa [hi] using hiv
      have hprePush : coveredBy x ((intervals.extract 0 i).push intervals[i]) :=
        (coveredBy_push_iff x (intervals.extract 0 i) intervals[i]).2 (Or.inr hiv')
      have : coveredBy x (intervals.extract 0 (i + 1)) := by
        rw [hextract]
        exact hprePush
      exact Or.inl this

  · intro h
    rcases h with hpre | hnew
    · -- turn prefix-coverage into pushed-prefix coverage
      have hprePush : coveredBy x ((intervals.extract 0 i).push intervals[i]) := by
        -- rewrite the assumption using hextract
        -- (rewriting in hypotheses)
        have hpre' := hpre
        rw [hextract] at hpre'
        exact hpre'
      have h2 : coveredBy x (intervals.extract 0 i) ∨ memInterval x intervals[i] :=
        (coveredBy_push_iff x (intervals.extract 0 i) intervals[i]).1 hprePush
      rcases h2 with hcovPre | hiv
      · have hres : coveredBy x res := hcov.mpr (Or.inl hcovPre)
        have hrespush : coveredBy x (res.push intervals[i]!) :=
          (coveredBy_push_iff x res (intervals[i]!)).2 (Or.inl hres)
        exact Or.inl hrespush
      · have hiv' : memInterval x intervals[i]! := by simpa [hi] using hiv
        have hrespush : coveredBy x (res.push intervals[i]!) :=
          (coveredBy_push_iff x res (intervals[i]!)).2 (Or.inr hiv')
        exact Or.inl hrespush
    · have hres : coveredBy x res := hcov.mpr (Or.inr hnew)
      have hrespush : coveredBy x (res.push intervals[i]!) :=
        (coveredBy_push_iff x res (intervals[i]!)).2 (Or.inl hres)
      exact Or.inl hrespush

theorem goal_1
    (intervals : Array Interval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (res : Array Interval)
    (invariant_inv_inserted_has_pending : true = true → ∃ j < res.size, res[j]! = (curStart, curEnd))
    : True → ∃ j < res.size + OfNat.ofNat 1, (res.push intervals[i]!)[j]! = (curStart, curEnd) := by
  intro _
  rcases invariant_inv_inserted_has_pending rfl with ⟨j, hj, hjEq⟩

  refine ⟨j, Nat.lt_trans hj (Nat.lt_succ_self res.size), ?_⟩

  -- show that `get!` at an old index is unchanged by `push`
  have hpush_get! : (res.push intervals[i]!).get! j = res.get! j := by
    -- rewrite get! via getD on getElem?
    simp [Array.get!_eq_getD]
    -- goal is now about getD of options
    have hop1 : (res.push intervals[i]!)[j]? = some res[j] := by
      simpa using (Array.getElem?_push_lt (xs := res) (x := intervals[i]!) (i := j) hj)
    have hopEq : (res.push intervals[i]!)[j]? = res[j]? := by
      have hne : j ≠ res.size := Nat.ne_of_lt hj
      simpa [Array.getElem?_push, hne] using
        (Array.getElem?_push (xs := res) (x := intervals[i]!) (i := j))
    have hop2 : res[j]? = some res[j] := by
      simpa [hopEq] using hop1
    -- finish by rewriting both sides
    simp [hop1, hop2]

  have hpush : (res.push intervals[i]!)[j]! = res[j]! := by
    simpa using hpush_get!

  simpa [hpush, hjEq]

theorem goal_2
    (intervals : Array Interval)
    (newInterval : Interval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (inserted : Bool)
    (res : Array Interval)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    (if_pos : i < intervals.size)
    : ∀ (x : ℤ), coveredBy x (res.push intervals[i]!) ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
  classical

  -- In bounds, `get!` agrees with `getElem`.
  have getBang_eq_getElem (xs : Array Interval) (n : Nat) (h : n < xs.size) :
      xs[n]! = xs[n]'h := by
    simp [Array.get!_eq_getD, Array.getD, h]

  -- Coverage characterization for `push`.
  have coveredBy_push_iff (x : Int) (xs : Array Interval) (iv : Interval) :
      coveredBy x (xs.push iv) ↔ coveredBy x xs ∨ memInterval x iv := by
    constructor
    · rintro ⟨j, hj, hjmem⟩
      have hj' : j < xs.size + 1 := by
        simpa [Array.size_push] using hj
      have hjle : j ≤ xs.size := Nat.le_of_lt_succ hj'
      have hj_cases : j < xs.size ∨ j = xs.size := lt_or_eq_of_le hjle
      cases hj_cases with
      | inl hjlt =>
          left
          refine ⟨j, hjlt, ?_⟩
          have hj_push : j < (xs.push iv).size := hj
          have hj_getBang : (xs.push iv)[j]! = (xs.push iv)[j]'hj_push := by
            simpa using (getBang_eq_getElem (xs := xs.push iv) (n := j) (h := hj_push))
          have hj_getElem : (xs.push iv)[j]'hj_push = xs[j]'hjlt := by
            have := (Array.getElem_push (xs := xs) (x := iv) (i := j) (h := hj_push))
            simpa [hjlt] using this
          have hj_getBang_xs : xs[j]! = xs[j]'hjlt := by
            simpa using (getBang_eq_getElem (xs := xs) (n := j) (h := hjlt))
          have : memInterval x (xs[j]'hjlt) := by
            simpa [hj_getBang, hj_getElem] using hjmem
          simpa [hj_getBang_xs] using this
      | inr hjeq =>
          right
          have hlast : xs.size < (xs.push iv).size := by
            simpa [Array.size_push] using Nat.lt_succ_self xs.size
          have hlast_getBang : (xs.push iv)[xs.size]! = (xs.push iv)[xs.size]'hlast := by
            simpa using (getBang_eq_getElem (xs := xs.push iv) (n := xs.size) (h := hlast))
          have hlast_getElem : (xs.push iv)[xs.size]'hlast = iv := by
            have := (Array.getElem_push (xs := xs) (x := iv) (i := xs.size) (h := hlast))
            simpa using this
          subst hjeq
          have : memInterval x iv := by
            simpa [hlast_getBang, hlast_getElem] using hjmem
          exact this

    · intro h
      cases h with
      | inl hcov =>
          rcases hcov with ⟨j, hjlt, hjmem⟩
          refine ⟨j, ?_, ?_⟩
          · have : j < xs.size + 1 := Nat.lt_succ_of_lt hjlt
            simpa [Array.size_push] using this
          · have hj_push : j < (xs.push iv).size := by
              have : j < xs.size + 1 := Nat.lt_succ_of_lt hjlt
              simpa [Array.size_push] using this
            have hj_getBang : (xs.push iv)[j]! = (xs.push iv)[j]'hj_push := by
              simpa using (getBang_eq_getElem (xs := xs.push iv) (n := j) (h := hj_push))
            have hj_getElem : (xs.push iv)[j]'hj_push = xs[j]'hjlt := by
              have := (Array.getElem_push (xs := xs) (x := iv) (i := j) (h := hj_push))
              simpa [hjlt] using this
            have hj_getBang_xs : xs[j]! = xs[j]'hjlt := by
              simpa using (getBang_eq_getElem (xs := xs) (n := j) (h := hjlt))
            have : memInterval x (xs[j]'hjlt) := by
              simpa [hj_getBang_xs] using hjmem
            simpa [hj_getBang, hj_getElem] using this
      | inr hmem =>
          refine ⟨xs.size, ?_, ?_⟩
          · simpa [Array.size_push] using Nat.lt_succ_self xs.size
          · have hlast : xs.size < (xs.push iv).size := by
              simpa [Array.size_push] using Nat.lt_succ_self xs.size
            have hlast_getBang : (xs.push iv)[xs.size]! = (xs.push iv)[xs.size]'hlast := by
              simpa using (getBang_eq_getElem (xs := xs.push iv) (n := xs.size) (h := hlast))
            have hlast_getElem : (xs.push iv)[xs.size]'hlast = iv := by
              have := (Array.getElem_push (xs := xs) (x := iv) (i := xs.size) (h := hlast))
              simpa using this
            simpa [hlast_getBang, hlast_getElem] using hmem

  -- `extract 0 (i+1)` is `extract 0 i` with the next element pushed.
  have hextract : intervals.extract 0 (i + 1) = (intervals.extract 0 i).push intervals[i]! := by
    have w : (0 : Nat) < i + 1 := Nat.succ_pos i
    have h0 : intervals.extract 0 (i + 1) = (intervals.extract 0 i).push intervals[i] := by
      -- use `@` to avoid naming the implicit argument `as` (a keyword)
      simpa using (@Array.extract_succ_right Interval intervals 0 i w if_pos)
    have hget : intervals[i] = intervals[i]! := by
      simpa using (getBang_eq_getElem (xs := intervals) (n := i) (h := if_pos)).symm
    simpa [hget] using h0

  intro x

  have hcov_res_push :
      coveredBy x (res.push intervals[i]!) ↔ coveredBy x res ∨ memInterval x intervals[i]! :=
    coveredBy_push_iff x res (intervals[i]!)

  have hcov_pref_push :
      coveredBy x ((intervals.extract 0 i).push intervals[i]!) ↔
        coveredBy x (intervals.extract 0 i) ∨ memInterval x intervals[i]! :=
    coveredBy_push_iff x (intervals.extract 0 i) (intervals[i]!)

  constructor
  · intro h
    cases h with
    | inl hcovPush =>
        have h' : coveredBy x res ∨ memInterval x intervals[i]! := (hcov_res_push).1 hcovPush
        cases h' with
        | inl hcovRes =>
            have hr : coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval :=
              (invariant_inv_coverage x).1 (Or.inl hcovRes)
            cases hr with
            | inl hcovPref =>
                have : coveredBy x ((intervals.extract 0 i).push intervals[i]!) :=
                  (hcov_pref_push).2 (Or.inl hcovPref)
                have : coveredBy x (intervals.extract 0 (i + 1)) := by
                  simpa [hextract] using this
                exact Or.inl this
            | inr hmemNew =>
                exact Or.inr hmemNew
        | inr hmemIv =>
            have : coveredBy x ((intervals.extract 0 i).push intervals[i]!) :=
              (hcov_pref_push).2 (Or.inr hmemIv)
            have : coveredBy x (intervals.extract 0 (i + 1)) := by
              simpa [hextract] using this
            exact Or.inl this
    | inr hpend =>
        have hr : coveredBy x (intervals.extract 0 i) ∨ memInterval x newInterval :=
          (invariant_inv_coverage x).1 (Or.inr hpend)
        cases hr with
        | inl hcovPref =>
            have : coveredBy x ((intervals.extract 0 i).push intervals[i]!) :=
              (hcov_pref_push).2 (Or.inl hcovPref)
            have : coveredBy x (intervals.extract 0 (i + 1)) := by
              simpa [hextract] using this
            exact Or.inl this
        | inr hmemNew =>
            exact Or.inr hmemNew

  · intro h
    cases h with
    | inl hcovSucc =>
        have hcovPushPref : coveredBy x ((intervals.extract 0 i).push intervals[i]!) := by
          simpa [hextract] using hcovSucc
        have h' : coveredBy x (intervals.extract 0 i) ∨ memInterval x intervals[i]! :=
          (hcov_pref_push).1 hcovPushPref
        cases h' with
        | inl hcovPref =>
            have hl : coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) :=
              (invariant_inv_coverage x).2 (Or.inl hcovPref)
            cases hl with
            | inl hcovRes =>
                have : coveredBy x (res.push intervals[i]!) :=
                  (hcov_res_push).2 (Or.inl hcovRes)
                exact Or.inl this
            | inr hpend =>
                exact Or.inr hpend
        | inr hmemIv =>
            have : coveredBy x (res.push intervals[i]!) :=
              (hcov_res_push).2 (Or.inr hmemIv)
            exact Or.inl this
    | inr hmemNew =>
        have hl : coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) :=
          (invariant_inv_coverage x).2 (Or.inr hmemNew)
        cases hl with
        | inl hcovRes =>
            have : coveredBy x (res.push intervals[i]!) :=
              (hcov_res_push).2 (Or.inl hcovRes)
            exact Or.inl this
        | inr hpend =>
            exact Or.inr hpend

theorem goal_3
    (intervals : Array Interval)
    (newInterval : Interval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (inserted : Bool)
    (res : Array Interval)
    (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd))
    (if_pos : i < intervals.size)
    (if_neg : ¬inserted = true)
    : ∀ (x : ℤ), coveredBy x ((res.push (curStart, curEnd)).push intervals[i]!) ∨ true = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
  classical

  have hins : inserted = false := by
    cases inserted with
    | false => rfl
    | true => cases if_neg rfl

  -- In-bounds lookup for option access.
  have getElem?_lt' (xs : Array Interval) {j : Nat} (hj : j < xs.size) :
      xs[j]? = some (xs[j]'hj) := by
    -- rewrite to `get?` and unfold
    have : xs.get? j = xs[j]? := by
      simpa using (Array.get?_eq_getElem? xs j)
    -- now use the definitional behavior of `get?`.
    -- `simp` knows the definition of `get?`.
    --
    -- goal: xs[j]? = some ...
    -- replace with xs.get? j
    rw [← this]
    simp [Array.get?, hj]

  -- `get!` agrees with bounded access when the index is in bounds.
  have get!_of_lt (xs : Array Interval) {j : Nat} (hj : j < xs.size) :
      xs[j]! = xs[j]'hj := by
    change xs.get! j = xs[j]'hj
    -- `get!` is option lookup followed by `getD`.
    simp [Array.get!_eq_getD_getElem?, getElem?_lt' xs hj]

  -- Helper facts about `get!` on push.
  have get!_push_of_lt {xs : Array Interval} {iv : Interval} {j : Nat} (hj : j < xs.size) :
      (xs.push iv)[j]! = xs[j]! := by
    have hpush : j < (xs.push iv).size := by
      simpa [Array.size_push] using Nat.lt_succ_of_lt hj
    calc
      (xs.push iv)[j]! = (xs.push iv)[j]'hpush := by
        simpa using (get!_of_lt (xs := xs.push iv) hpush)
      _ = xs[j]'hj := by
        simpa [Array.getElem_push, hj] using
          (Array.getElem_push (xs := xs) (x := iv) (i := j) hpush)
      _ = xs[j]! := by
        symm
        simpa using (get!_of_lt (xs := xs) hj)

  have get!_push_size (xs : Array Interval) (iv : Interval) :
      (xs.push iv)[xs.size]! = iv := by
    have hpush : xs.size < (xs.push iv).size := by
      simpa [Array.size_push] using Nat.lt_succ_self xs.size
    calc
      (xs.push iv)[xs.size]! = (xs.push iv)[xs.size]'hpush := by
        simpa using (get!_of_lt (xs := xs.push iv) hpush)
      _ = iv := by
        simpa [Array.getElem_push] using
          (Array.getElem_push (xs := xs) (x := iv) (i := xs.size) hpush)

  -- Coverage over a push splits into old coverage or membership in the pushed interval.
  have coveredBy_push (x : Int) (xs : Array Interval) (iv : Interval) :
      coveredBy x (xs.push iv) ↔ coveredBy x xs ∨ memInterval x iv := by
    constructor
    · rintro ⟨j, hj, hjmem⟩
      have hj' : j < xs.size + 1 := by
        simpa [Array.size_push] using hj
      have hjle : j ≤ xs.size := Nat.lt_succ_iff.mp hj'
      have hcases : j < xs.size ∨ j = xs.size := lt_or_eq_of_le hjle
      cases hcases with
      | inl hjlt =>
          left
          refine ⟨j, hjlt, ?_⟩
          have hget : (xs.push iv)[j]! = xs[j]! := get!_push_of_lt (xs := xs) (iv := iv) hjlt
          simpa [hget] using hjmem
      | inr hjeq =>
          right
          subst hjeq
          have hget : (xs.push iv)[xs.size]! = iv := get!_push_size xs iv
          simpa [hget] using hjmem
    · intro h
      cases h with
      | inl hcov =>
          rcases hcov with ⟨j, hjlt, hjmem⟩
          refine ⟨j, ?_, ?_⟩
          · simpa [Array.size_push] using Nat.lt_succ_of_lt hjlt
          · have hget : (xs.push iv)[j]! = xs[j]! := get!_push_of_lt (xs := xs) (iv := iv) hjlt
            simpa [hget] using hjmem
      | inr hmem =>
          refine ⟨xs.size, ?_, ?_⟩
          · simpa [Array.size_push] using Nat.lt_succ_self xs.size
          · have hget : (xs.push iv)[xs.size]! = iv := get!_push_size xs iv
            simpa [hget] using hmem

  have invCov0 : ∀ x : Int,
      (coveredBy x res ∨ memInterval x (curStart, curEnd)) ↔
        (coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval) := by
    intro x
    simpa [hins] using (invariant_inv_coverage x)

  have invCov' : ∀ x : Int,
      coveredBy x (res.push (curStart, curEnd)) ∨ true = false ∧ memInterval x (curStart, curEnd) ↔
        coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval := by
    intro x
    have : coveredBy x (res.push (curStart, curEnd)) ↔
        coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval := by
      calc
        coveredBy x (res.push (curStart, curEnd))
            ↔ coveredBy x res ∨ memInterval x (curStart, curEnd) := by
                simpa using (coveredBy_push x res (curStart, curEnd))
        _ ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval := invCov0 x
    simpa using this

  simpa using
    (goal_0 intervals newInterval curEnd curStart i (res.push (curStart, curEnd)) if_pos invCov')

theorem goal_4
    (intervals : Array Interval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (res : Array Interval)
    : ∃ j < res.size + OfNat.ofNat 1 + OfNat.ofNat 1, ((res.push (curStart, curEnd)).push intervals[i]!)[j]! = (curStart, curEnd) := by
  classical

  set iv : Interval := intervals[i]! with hiv

  refine ⟨res.size, ?_, ?_⟩
  · -- bound
    have hpos : (0 : Nat) < (1 + 1) := by decide
    simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (a := res.size) hpos)

  · -- value at that index
    have hbound : res.size < ((res.push (curStart, curEnd)).push iv).size := by
      have hpos : (0 : Nat) < (1 + 1) := by decide
      simpa [Array.size_push, Nat.add_assoc] using (Nat.lt_add_of_pos_right (a := res.size) hpos)

    have hlt : res.size < (res.push (curStart, curEnd)).size := by
      simpa [Array.size_push, Nat.succ_eq_add_one] using (Nat.lt.base res.size)

    have hgetElem : ((res.push (curStart, curEnd)).push iv)[res.size] = (curStart, curEnd) := by
      have htmp := (Array.getElem_push (xs := res.push (curStart, curEnd)) (x := iv) (i := res.size) hbound)
      have htmp' : ((res.push (curStart, curEnd)).push iv)[res.size] =
          (res.push (curStart, curEnd))[res.size] := by
        simpa [hlt] using htmp
      simpa [Array.getElem_push_eq] using htmp'

    -- express the in-bounds fact in the arithmetic form that simp produces
    have hbound' : res.size < res.size + 1 + 1 := by
      have hpos : (0 : Nat) < (1 + 1) := by decide
      simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (a := res.size) hpos)

    have hgetBang : ((res.push (curStart, curEnd)).push iv)[res.size]! = (curStart, curEnd) := by
      -- unfold getElem! (i.e., getD), then discharge the bounds test with hbound'
      simp [Array.getElem!_eq_getD, Array.getD, Array.size_push, Nat.add_assoc, hbound', hgetElem]

    simpa [← hiv] using hgetBang



theorem goal_5
    (intervals : Array Interval)
    (newInterval : Interval)
    (require_1 : precondition intervals newInterval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (inserted : Bool)
    (res : Array Interval)
    (invariant_inv_i_bounds : i ≤ intervals.size)
    (invariant_inv_pending_wf : curStart ≤ curEnd)
    (invariant_inv_res_canonical : canonical res)
    (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!)
    (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd))
    (if_pos : i < intervals.size)
    (if_neg : ¬inserted = true)
    (if_neg_1 : ¬iend intervals[i]! < curStart)
    (if_neg_2 : ¬curEnd < istart intervals[i]!)
    (if_pos_1 : istart intervals[i]! < curStart)
    (if_pos_2 : curEnd < iend intervals[i]!)
    : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (istart intervals[i]!, iend intervals[i]!) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    sorry

theorem goal_6
    (intervals : Array Interval)
    (newInterval : Interval)
    (require_1 : precondition intervals newInterval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (inserted : Bool)
    (res : Array Interval)
    (invariant_inv_i_bounds : i ≤ intervals.size)
    (invariant_inv_pending_wf : curStart ≤ curEnd)
    (invariant_inv_res_canonical : canonical res)
    (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!)
    (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd))
    (if_pos : i < intervals.size)
    (if_neg : ¬inserted = true)
    (if_neg_1 : ¬iend intervals[i]! < curStart)
    (if_neg_2 : ¬curEnd < istart intervals[i]!)
    (if_pos_1 : istart intervals[i]! < curStart)
    (if_neg_3 : ¬curEnd < iend intervals[i]!)
    : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (istart intervals[i]!, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    sorry

theorem goal_7
    (intervals : Array Interval)
    (newInterval : Interval)
    (require_1 : precondition intervals newInterval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (inserted : Bool)
    (res : Array Interval)
    (invariant_inv_i_bounds : i ≤ intervals.size)
    (invariant_inv_pending_wf : curStart ≤ curEnd)
    (invariant_inv_res_canonical : canonical res)
    (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!)
    (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd))
    (if_pos : i < intervals.size)
    (if_neg : ¬inserted = true)
    (if_neg_1 : ¬iend intervals[i]! < curStart)
    (if_neg_2 : ¬curEnd < istart intervals[i]!)
    (if_neg_3 : ¬istart intervals[i]! < curStart)
    (if_pos_1 : curEnd < iend intervals[i]!)
    : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, iend intervals[i]!) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    sorry

theorem goal_8
    (intervals : Array Interval)
    (newInterval : Interval)
    (require_1 : precondition intervals newInterval)
    (curEnd : ℤ)
    (curStart : ℤ)
    (i : ℕ)
    (inserted : Bool)
    (res : Array Interval)
    (invariant_inv_i_bounds : i ≤ intervals.size)
    (invariant_inv_pending_wf : curStart ≤ curEnd)
    (invariant_inv_res_canonical : canonical res)
    (invariant_inv_last_before_next_input : i < intervals.size → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < istart intervals[i]!)
    (invariant_inv_last_before_pending : inserted = false → res.size = OfNat.ofNat 0 ∨ iend res[res.size - OfNat.ofNat 1]! < curStart)
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i) ∨ memInterval x newInterval)
    (invariant_inv_inserted_has_pending : inserted = true → ∃ j < res.size, res[j]! = (curStart, curEnd))
    (if_pos : i < intervals.size)
    (if_neg : ¬inserted = true)
    (if_neg_1 : ¬iend intervals[i]! < curStart)
    (if_neg_2 : ¬curEnd < istart intervals[i]!)
    (if_neg_3 : ¬istart intervals[i]! < curStart)
    (if_neg_4 : ¬curEnd < iend intervals[i]!)
    : ∀ (x : ℤ), coveredBy x res ∨ inserted = false ∧ memInterval x (curStart, curEnd) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) ∨ memInterval x newInterval := by
    sorry

theorem goal_9
    (intervals : Array Interval)
    (newInterval : Interval)
    (require_1 : precondition intervals newInterval)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (res_1 : Array Interval)
    (invariant_inv_pending_wf : i_2 ≤ i_1)
    (invariant_inv_i_bounds : i_3 ≤ intervals.size)
    (done_1 : ¬i_3 < intervals.size)
    (invariant_inv_res_canonical : canonical res_1)
    (invariant_inv_last_before_next_input : i_3 < intervals.size → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < istart intervals[i_3]!)
    (invariant_inv_last_before_pending : false = false → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < i_2)
    (invariant_inv_inserted_has_pending : false = true → ∃ j < res_1.size, res_1[j]! = (i_2, i_1))
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res_1 ∨ false = false ∧ memInterval x (i_2, i_1) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i_3) ∨ memInterval x newInterval)
    : postcondition intervals newInterval (res_1.push (i_2, i_1)) := by
    sorry

theorem goal_10
    (intervals : Array Interval)
    (newInterval : Interval)
    (require_1 : precondition intervals newInterval)
    (i_1 : ℤ)
    (i_2 : ℤ)
    (i_3 : ℕ)
    (i_4 : Bool)
    (res_1 : Array Interval)
    (if_neg : ¬i_4 = false)
    (invariant_inv_pending_wf : i_2 ≤ i_1)
    (invariant_inv_i_bounds : i_3 ≤ intervals.size)
    (done_1 : ¬i_3 < intervals.size)
    (invariant_inv_res_canonical : canonical res_1)
    (invariant_inv_last_before_next_input : i_3 < intervals.size → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < istart intervals[i_3]!)
    (invariant_inv_last_before_pending : i_4 = false → res_1.size = OfNat.ofNat 0 ∨ iend res_1[res_1.size - OfNat.ofNat 1]! < i_2)
    (invariant_inv_inserted_has_pending : i_4 = true → ∃ j < res_1.size, res_1[j]! = (i_2, i_1))
    (invariant_inv_coverage : ∀ (x : ℤ), coveredBy x res_1 ∨ i_4 = false ∧ memInterval x (i_2, i_1) ↔ coveredBy x (intervals.extract (OfNat.ofNat 0) i_3) ∨ memInterval x newInterval)
    : postcondition intervals newInterval res_1 := by
    sorry



prove_correct InsertInterval by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 intervals newInterval curEnd curStart i res if_pos invariant_inv_coverage)
  exact (goal_1 intervals curEnd curStart i res invariant_inv_inserted_has_pending)
  exact (goal_2 intervals newInterval curEnd curStart i inserted res invariant_inv_coverage if_pos)
  exact (goal_3 intervals newInterval curEnd curStart i inserted res invariant_inv_last_before_pending invariant_inv_coverage invariant_inv_inserted_has_pending if_pos if_neg)
  exact (goal_4 intervals curEnd curStart i res)
  exact (goal_5 intervals newInterval require_1 curEnd curStart i inserted res invariant_inv_i_bounds invariant_inv_pending_wf invariant_inv_res_canonical invariant_inv_last_before_next_input invariant_inv_last_before_pending invariant_inv_coverage invariant_inv_inserted_has_pending if_pos if_neg if_neg_1 if_neg_2 if_pos_1 if_pos_2)
  exact (goal_6 intervals newInterval require_1 curEnd curStart i inserted res invariant_inv_i_bounds invariant_inv_pending_wf invariant_inv_res_canonical invariant_inv_last_before_next_input invariant_inv_last_before_pending invariant_inv_coverage invariant_inv_inserted_has_pending if_pos if_neg if_neg_1 if_neg_2 if_pos_1 if_neg_3)
  exact (goal_7 intervals newInterval require_1 curEnd curStart i inserted res invariant_inv_i_bounds invariant_inv_pending_wf invariant_inv_res_canonical invariant_inv_last_before_next_input invariant_inv_last_before_pending invariant_inv_coverage invariant_inv_inserted_has_pending if_pos if_neg if_neg_1 if_neg_2 if_neg_3 if_pos_1)
  exact (goal_8 intervals newInterval require_1 curEnd curStart i inserted res invariant_inv_i_bounds invariant_inv_pending_wf invariant_inv_res_canonical invariant_inv_last_before_next_input invariant_inv_last_before_pending invariant_inv_coverage invariant_inv_inserted_has_pending if_pos if_neg if_neg_1 if_neg_2 if_neg_3 if_neg_4)
  exact (goal_9 intervals newInterval require_1 i_1 i_2 i_3 res_1 invariant_inv_pending_wf invariant_inv_i_bounds done_1 invariant_inv_res_canonical invariant_inv_last_before_next_input invariant_inv_last_before_pending invariant_inv_inserted_has_pending invariant_inv_coverage)
  exact (goal_10 intervals newInterval require_1 i_1 i_2 i_3 i_4 res_1 if_neg invariant_inv_pending_wf invariant_inv_i_bounds done_1 invariant_inv_res_canonical invariant_inv_last_before_next_input invariant_inv_last_before_pending invariant_inv_inserted_has_pending invariant_inv_coverage)
end Proof
