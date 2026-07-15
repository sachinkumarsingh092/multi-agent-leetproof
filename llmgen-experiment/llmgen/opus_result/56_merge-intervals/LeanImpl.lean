import Lean
import Mathlib.Tactic
import Velvet.Std
import Extensions.VelvetPBT

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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_intervals), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_intervals), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_intervals), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_intervals), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_intervals), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_intervals), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_intervals), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_intervals), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_intervals), test9_Expected]
end Assertions

section Pbt
method implementationPbt (intervals : Array Interval)
  return (result : Array Interval)
  require precondition intervals
  ensures postcondition intervals result
  do
  return (implementation intervals)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
private lemma AllValid_push (a : Array Interval) (iv : Interval) :
    AllValid (a.push iv) ↔ AllValid a ∧ istart iv ≤ iend iv := by
  unfold AllValid
  simp [Array.size_push]
  constructor
  · intro h
    constructor
    · intro i hi
      have hi' : i < a.size + 1 := by omega
      specialize h i hi'
      have : (a.push iv)[i]! = a[i]! := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
        simp [Array.getElem?_push]
        have : ¬ (i = a.size) := by omega
        simp [this]
      rw [this] at h
      exact h
    · specialize h a.size (by omega)
      have : (a.push iv)[a.size]! = iv := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rw [this] at h
      exact h
  · intro ⟨ha, hiv⟩ i hi
    by_cases hlt : i < a.size
    · have : (a.push iv)[i]! = a[i]! := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
        simp [Array.getElem?_push]
        have : ¬ (i = a.size) := by omega
        simp [this]
      rw [this]
      exact ha i hlt
    · have heq : i = a.size := by omega
      subst heq
      have : (a.push iv)[a.size]! = iv := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rw [this]
      exact hiv

private lemma foldl_merge_invariant
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sz : 0 < intervals.size) :
    let f : Array Interval × Interval → Interval → Array Interval × Interval :=
      fun acc iv =>
        let (merged, current) := acc
        if iv.1 ≤ current.2 then (merged, (current.1, max current.2 iv.2)) else (merged.push current, iv)
    let result := (intervals.extract 1 intervals.size).foldl f (#[], intervals[0]!)
    AllValid result.1 ∧ istart result.2 ≤ iend result.2 := by
  intro f result
  set arr := intervals.extract 1 intervals.size with harr
  apply Array.foldl_induction (as := arr)
    (motive := fun _ (acc : Array Interval × Interval) => AllValid acc.1 ∧ istart acc.2 ≤ iend acc.2)
  -- Base case
  · constructor
    · intro i hi; simp [Array.size_empty] at hi
    · exact h_valid 0 h_sz
  -- Inductive step
  · intro ⟨i, hi⟩ ⟨merged, current⟩ ⟨h_valid_merged, h_cur_valid⟩
    show (fun _ acc => AllValid acc.1 ∧ istart acc.2 ≤ iend acc.2) (↑i + 1) (f (merged, current) arr[i])
    simp only [f]
    -- arr[i] comes from intervals
    have hi_orig : 1 + i < intervals.size := by
      simp [harr, Array.size_extract] at hi; omega
    have h_iv_valid : (arr[i]).1 ≤ (arr[i]).2 := by
      have : arr[i] = intervals[1 + i]'(by omega) := by
        simp [harr, Array.getElem_extract]
      rw [this]
      have h_v := h_valid (1 + i) hi_orig
      simp [istart, iend, Array.getElem!_eq_getD, Array.getD_getElem?,
            Array.getElem?_eq_getElem (h := hi_orig)] at h_v
      exact h_v
    split
    · -- Merge case
      exact ⟨h_valid_merged, le_trans h_cur_valid (Int.le_max_left _ _)⟩
    · -- Push case
      constructor
      · rw [AllValid_push]; exact ⟨h_valid_merged, h_cur_valid⟩
      · simp only [istart, iend]; exact h_iv_valid


theorem correctness_goal_0_0
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sz : 0 < intervals.size)
    : AllValid
    (Array.foldl
        (fun acc iv =>
          Prod.casesOn acc fun fst snd =>
            (fun merged current =>
                if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
              fst snd)
        (#[], intervals[0]!) intervals 1).1 ∧
  istart
      (Array.foldl
          (fun acc iv =>
            Prod.casesOn acc fun fst snd =>
              (fun merged current =>
                  if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                fst snd)
          (#[], intervals[0]!) intervals 1).2 ≤
    iend
      (Array.foldl
          (fun acc iv =>
            Prod.casesOn acc fun fst snd =>
              (fun merged current =>
                  if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                fst snd)
          (#[], intervals[0]!) intervals 1).2 := by
  let f : Array Interval × Interval → Interval → Array Interval × Interval :=
    fun acc iv =>
      let (merged, current) := acc
      if iv.1 ≤ current.2 then (merged, (current.1, max current.2 iv.2)) else (merged.push current, iv)
  -- Show the fold functions are equal
  have h_eq : intervals.foldl (fun acc iv =>
          Prod.casesOn acc fun fst snd =>
            (fun merged current =>
                if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
              fst snd) (#[], intervals[0]!) 1 =
    intervals.foldl f (#[], intervals[0]!) 1 := by congr 1
  simp only [h_eq]
  -- Rewrite foldl with start=1 to foldl on extract
  rw [show intervals.foldl f (#[], intervals[0]!) 1 = (intervals.extract 1 intervals.size).foldl f (#[], intervals[0]!) from by
    rw [Array.foldl_eq_foldlM, Array.foldlM_start_stop, ← Array.foldl_eq_foldlM]]
  exact foldl_merge_invariant intervals h_valid h_sz

theorem correctness_goal_0
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    : AllValid (implementation intervals) := by
  unfold implementation
  simp only [beq_iff_eq]
  split
  · -- intervals.size = 0
    unfold AllValid
    simp
  · -- intervals.size ≠ 0
    rename_i h_ne
    have h_sz : 0 < intervals.size := by omega
    -- The fold invariant: AllValid merged ∧ istart current ≤ iend current
    have h_fold_inv : AllValid (intervals.foldl (fun (acc : Array Interval × Interval) (iv : Interval) =>
      let (merged, current) := acc
      if iv.1 ≤ current.2 then
        (merged, (current.1, max current.2 iv.2))
      else
        (merged.push current, iv)
    ) (#[], intervals[0]!) 1).1 ∧
    istart (intervals.foldl (fun (acc : Array Interval × Interval) (iv : Interval) =>
      let (merged, current) := acc
      if iv.1 ≤ current.2 then
        (merged, (current.1, max current.2 iv.2))
      else
        (merged.push current, iv)
    ) (#[], intervals[0]!) 1).2 ≤
    iend (intervals.foldl (fun (acc : Array Interval × Interval) (iv : Interval) =>
      let (merged, current) := acc
      if iv.1 ≤ current.2 then
        (merged, (current.1, max current.2 iv.2))
      else
        (merged.push current, iv)
    ) (#[], intervals[0]!) 1).2 := by expose_names; exact (correctness_goal_0_0 intervals h_valid h_sz)
    rw [AllValid_push]
    exact h_fold_inv

lemma LexSorted_implies_nondec_starts (intervals : Array Interval) (h : LexSortedIntervals intervals) :
    ∀ (i : Nat), i + 1 < intervals.size → istart intervals[i]! ≤ istart intervals[i+1]! := by
  intro i hi
  have := h i hi
  rcases this with h1 | h2 | h3
  · exact Int.le_of_lt h1
  · exact le_of_eq h2.1
  · exact le_of_eq h3.1

lemma nondec_starts_trans (intervals : Array Interval)
    (h : ∀ (i : Nat), i + 1 < intervals.size → istart intervals[i]! ≤ istart intervals[i+1]!)
    (i j : Nat) (hij : i ≤ j) (hj : j < intervals.size) (hi : i < intervals.size) :
    istart intervals[i]! ≤ istart intervals[j]! := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  induction k with
  | zero => simp
  | succ n ih =>
    have hn : i + n < intervals.size := by omega
    have ih' := ih (by omega) hn
    have := h (i + n) (by omega)
    exact le_trans ih' this

lemma getElem!_push_lt {α : Type*} [Inhabited α] {a : Array α} {v : α} {i : Nat} (h : i < a.size) :
    (a.push v)[i]! = a[i]! := by
  have h' : i < (a.push v).size := by simp [Array.size_push]; omega
  rw [getElem!_pos (a.push v) i h', getElem!_pos a i h]
  exact Array.getElem_push_lt h

lemma getElem!_push_eq {α : Type*} [Inhabited α] {a : Array α} {v : α} :
    (a.push v)[a.size]! = v := by
  have h : a.size < (a.push v).size := by simp [Array.size_push]
  rw [getElem!_pos (a.push v) a.size h]
  exact Array.getElem_push_eq

lemma NondecreasingStarts_push (a : Array Interval) (iv : Interval) :
    NondecreasingStarts (a.push iv) ↔ NondecreasingStarts a ∧ (0 < a.size → istart a[a.size - 1]! ≤ istart iv) := by
  unfold NondecreasingStarts
  constructor
  · intro h
    constructor
    · intro i hi
      have hi' : i + 1 < (a.push iv).size := by simp [Array.size_push]; omega
      have := h i hi'
      rw [getElem!_push_lt (by omega : i < a.size), getElem!_push_lt (by omega : i + 1 < a.size)] at this
      exact this
    · intro hsz
      have hlt : a.size - 1 + 1 < (a.push iv).size := by simp [Array.size_push]; omega
      have := h (a.size - 1) hlt
      rw [getElem!_push_lt (by omega : a.size - 1 < a.size)] at this
      have heq : a.size - 1 + 1 = a.size := by omega
      rw [heq] at this
      rw [getElem!_push_eq] at this
      exact this
  · intro ⟨hnd, hlast⟩
    intro i hi
    have hsz : (a.push iv).size = a.size + 1 := Array.size_push _
    by_cases h1 : i + 1 < a.size
    · rw [getElem!_push_lt (by omega : i < a.size), getElem!_push_lt h1]
      exact hnd i h1
    · have h2 : i + 1 = a.size := by omega
      have h3 : i < a.size := by omega
      rw [getElem!_push_lt h3]
      have h5 : i = a.size - 1 := by omega
      rw [h5]
      have h4 : (a.push iv)[a.size - 1 + 1]! = iv := by
        have : a.size - 1 + 1 = a.size := by omega
        rw [this]
        exact getElem!_push_eq
      rw [h4]
      exact hlast (by omega)

lemma NondecreasingStarts_empty : NondecreasingStarts #[] := by
  intro i hi
  simp [Array.size] at hi

-- Convert foldl with start to foldl on extract
lemma foldl_start_eq_extract_foldl {α β : Type*} (f : β → α → β) (init : β) (xs : Array α) (start : Nat) :
    xs.foldl f init start = (xs.extract start xs.size).foldl f init := by
  rw [Array.foldl_eq_foldlM, Array.foldlM_start_stop, ← Array.foldl_eq_foldlM]


theorem correctness_goal_1_0
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sorted : LexSortedIntervals intervals)
    (h_allvalid : AllValid (implementation intervals))
    (h_empty : ¬(intervals.size == 0) = true)
    (h_sz : 0 < intervals.size)
    (h_nondec_starts_input : ∀ (i : ℕ), i + 1 < intervals.size → istart intervals[i]! ≤ istart intervals[i + 1]!)
    : NondecreasingStarts
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


theorem correctness_goal_1
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sorted : LexSortedIntervals intervals)
    (h_allvalid : AllValid (implementation intervals))
    : NondecreasingStarts (implementation intervals) := by
    unfold implementation
    by_cases h_empty : intervals.size == 0
    · simp [h_empty]
      unfold NondecreasingStarts
      intro i hi
      simp at hi
    · simp [h_empty]
      have h_sz : 0 < intervals.size := by
        by_contra h
        push_neg at h
        interval_cases intervals.size <;> simp_all
      have h_nondec_starts_input : ∀ (i : Nat), i + 1 < intervals.size → istart intervals[i]! ≤ istart intervals[i+1]! :=
        LexSorted_implies_nondec_starts intervals h_sorted

      have h_inv : NondecreasingStarts
          (Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).1 ∧
        (0 < (Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).1.size →
          istart (Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).1[(Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).1.size - 1]! ≤
          istart (Array.foldl
            (fun acc iv =>
              Prod.casesOn acc fun fst snd =>
                (fun merged current =>
                    if iv.1 ≤ current.2 then (merged, current.1, max current.2 iv.2) else (merged.push current, iv))
                  fst snd)
            (#[], intervals[0]!) intervals 1).2) := by expose_names; exact (correctness_goal_1_0 intervals h_valid h_sorted h_allvalid h_empty h_sz h_nondec_starts_input)

      rw [NondecreasingStarts_push]
      exact h_inv

theorem correctness_goal_2
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sorted : LexSortedIntervals intervals)
    (h_allvalid : AllValid (implementation intervals))
    (h_nondec : NondecreasingStarts (implementation intervals))
    : StrictlyNonOverlapping (implementation intervals) := by
    sorry


theorem correctness_goal_3
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sorted : LexSortedIntervals intervals)
    (h_allvalid : AllValid (implementation intervals))
    (h_nondec : NondecreasingStarts (implementation intervals))
    (h_nonoverlap : StrictlyNonOverlapping (implementation intervals))
    : ∀ (x : ℤ), CoveredBy x (implementation intervals) ↔ CoveredBy x intervals := by
    sorry


theorem correctness_goal_4
    (intervals : Array Interval)
    (h_valid : AllValid intervals)
    (h_sorted : LexSortedIntervals intervals)
    (h_allvalid : AllValid (implementation intervals))
    (h_nondec : NondecreasingStarts (implementation intervals))
    (h_nonoverlap : StrictlyNonOverlapping (implementation intervals))
    (h_coverage : ∀ (x : ℤ), CoveredBy x (implementation intervals) ↔ CoveredBy x intervals)
    : ∀ i < (implementation intervals).size, IntervalIsTight intervals (implementation intervals)[i]! := by
    sorry



theorem correctness_goal
    (intervals : Array Interval)
    (h_precond : precondition intervals)
    : postcondition intervals (implementation intervals) := by
    unfold precondition at h_precond
    obtain ⟨h_valid, h_sorted⟩ := h_precond
    unfold postcondition
    have h_allvalid : AllValid (implementation intervals) := by expose_names; exact (correctness_goal_0 intervals h_valid)
    have h_nondec : NondecreasingStarts (implementation intervals) := by expose_names; exact (correctness_goal_1 intervals h_valid h_sorted h_allvalid)
    have h_nonoverlap : StrictlyNonOverlapping (implementation intervals) := by expose_names; exact (correctness_goal_2 intervals h_valid h_sorted h_allvalid h_nondec)
    have h_coverage : ∀ (x : Int), CoveredBy x (implementation intervals) ↔ CoveredBy x intervals := by expose_names; exact (correctness_goal_3 intervals h_valid h_sorted h_allvalid h_nondec h_nonoverlap)
    have h_tight : ∀ (i : Nat), i < (implementation intervals).size → IntervalIsTight intervals (implementation intervals)[i]! := by expose_names; exact (correctness_goal_4 intervals h_valid h_sorted h_allvalid h_nondec h_nonoverlap h_coverage)
    exact ⟨h_allvalid, h_nondec, h_nonoverlap, h_coverage, h_tight⟩
end Proof
