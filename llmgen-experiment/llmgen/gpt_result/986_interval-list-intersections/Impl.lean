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
    IntervalListIntersections: Intersect two sorted, pairwise-disjoint lists of closed integer intervals.
    Natural language breakdown:
    1. Each interval is a pair (start, end) representing the closed set of integers {x | start ≤ x ∧ x ≤ end}.
    2. Each input list is sorted by start ascending.
    3. Intervals in the same list are pairwise disjoint (non-overlapping); because they are closed, disjointness means the end of one is strictly less than the start of the next.
    4. The output is the list of all non-empty intersections between an interval from the first list and an interval from the second list.
    5. Each intersection of two closed intervals is either empty or a closed interval [max starts, min ends].
    6. The output list should be sorted and pairwise disjoint.
    7. Semantically, the union of the output intervals equals the set intersection of the unions of the input interval sets.
    Your algorithm should run in **O(m+n)** time and **O(1)** extra space, where m and n are the sizes of the two input lists.
-/

section Specs
-- An interval is represented as a pair (start, end).
abbrev Interval := Int × Int

-- Convert an interval to the set of integers it denotes.
def intervalSet (iv : Interval) : Set Int :=
  Set.Icc iv.1 iv.2

-- The interval is well-formed.
def isValidInterval (iv : Interval) : Prop :=
  iv.1 ≤ iv.2

-- Array is sorted by starts (nondecreasing).
def sortedByStart (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.1 ≤ a[j]!.1

-- Array is pairwise disjoint in the strong closed-interval sense.
-- This implies that whenever i < j, the i-th interval ends strictly before the j-th interval begins.
def pairwiseDisjointClosed (a : Array Interval) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]!.2 < a[j]!.1

-- The union of all interval sets represented by an array.
def unionIntervalSets (a : Array Interval) : Set Int :=
  {x : Int | ∃ (i : Nat), i < a.size ∧ x ∈ intervalSet a[i]!}

-- Precondition: both lists contain only valid intervals and are sorted/disjoint.
def precondition (firstList : Array Interval) (secondList : Array Interval) : Prop :=
  (∀ (i : Nat), i < firstList.size → isValidInterval firstList[i]!) ∧
  (∀ (i : Nat), i < secondList.size → isValidInterval secondList[i]!) ∧
  sortedByStart firstList ∧
  sortedByStart secondList ∧
  pairwiseDisjointClosed firstList ∧
  pairwiseDisjointClosed secondList

-- Postcondition: output is a valid sorted/disjoint interval list whose union equals the set intersection
-- of the unions of input lists.
def postcondition (firstList : Array Interval) (secondList : Array Interval)
  (result : Array Interval) : Prop :=
  (∀ (k : Nat), k < result.size → isValidInterval result[k]!) ∧
  sortedByStart result ∧
  pairwiseDisjointClosed result ∧
  unionIntervalSets result = (unionIntervalSets firstList ∩ unionIntervalSets secondList)
end Specs

section Impl
method IntervalListIntersections (firstList : Array Interval) (secondList : Array Interval)
  return (result : Array Interval)
  require precondition firstList secondList
  ensures postcondition firstList secondList result
  do
    let mut i : Nat := 0
    let mut j : Nat := 0
    let mut out : Array Interval := #[]

    while (i < firstList.size ∧ j < secondList.size)
      -- Indices stay within bounds.
      -- Init: i=j=0. Preserved: each step increments i or j, and both are Nat.
      invariant "inv_bounds" (i ≤ firstList.size ∧ j ≤ secondList.size)
      -- Produced intervals are valid.
      -- Init: vacuous for empty out. Preserved: we only push (s,e) when s ≤ e.
      invariant "inv_out_valid" (∀ (k : Nat), k < out.size → isValidInterval out[k]!)
      -- Produced intervals are sorted by start.
      -- Init: empty array sorted. Preserved by the sweep order implied by sorted/disjoint inputs.
      invariant "inv_out_sorted" (sortedByStart out)
      -- Produced intervals are pairwise disjoint.
      -- Init: empty array disjoint. Preserved by the sweep order implied by sorted/disjoint inputs.
      invariant "inv_out_disjoint" (pairwiseDisjointClosed out)
      -- Semantic meaning: out contains exactly the intersection contributed by the processed
      -- prefixes (either side processed against the full other list).
      -- This is what allows proving the final union equality when one side is exhausted.
      invariant "inv_semantic"
        (unionIntervalSets out =
          ((unionIntervalSets (firstList.take i) ∩ unionIntervalSets secondList) ∪
           (unionIntervalSets firstList ∩ unionIntervalSets (secondList.take j))))
      -- Loop terminates when either list is exhausted.
      done_with (i = firstList.size ∨ j = secondList.size)
      decreasing (firstList.size - i) + (secondList.size - j)
    do
      let a := firstList[i]!
      let b := secondList[j]!

      let s := if a.1 ≥ b.1 then a.1 else b.1
      let e := if a.2 ≤ b.2 then a.2 else b.2

      if s ≤ e then
        out := out.push (s, e)

      if a.2 < b.2 then
        i := i + 1
      else
        j := j + 1

    return out
end Impl

section TestCases
-- Test case 1: Example 1 from the prompt
-- firstList = [[0,2],[5,10],[13,23],[24,25]]
-- secondList = [[1,5],[8,12],[15,24],[25,26]]
-- expected = [[1,2],[5,5],[8,10],[15,23],[24,24],[25,25]]
def test1_firstList : Array Interval := #[(0,2),(5,10),(13,23),(24,25)]
def test1_secondList : Array Interval := #[(1,5),(8,12),(15,24),(25,26)]
def test1_Expected : Array Interval := #[(1,2),(5,5),(8,10),(15,23),(24,24),(25,25)]

-- Test case 2: Example 2 from the prompt (second list empty)
def test2_firstList : Array Interval := #[(1,3),(5,9)]
def test2_secondList : Array Interval := #[]
def test2_Expected : Array Interval := #[]

-- Test case 3: first list empty

def test3_firstList : Array Interval := #[]
def test3_secondList : Array Interval := #[(1,2)]
def test3_Expected : Array Interval := #[]

-- Test case 4: both lists empty

def test4_firstList : Array Interval := #[]
def test4_secondList : Array Interval := #[]
def test4_Expected : Array Interval := #[]

-- Test case 5: single interval overlaps producing a non-degenerate intersection

def test5_firstList : Array Interval := #[(1,5)]
def test5_secondList : Array Interval := #[(2,3)]
def test5_Expected : Array Interval := #[(2,3)]

-- Test case 6: single interval intersection is a point

def test6_firstList : Array Interval := #[(1,2)]
def test6_secondList : Array Interval := #[(2,4)]
def test6_Expected : Array Interval := #[(2,2)]

-- Test case 7: no overlaps at all

def test7_firstList : Array Interval := #[(1,2)]
def test7_secondList : Array Interval := #[(3,4)]
def test7_Expected : Array Interval := #[]

-- Test case 8: negative numbers and multiple intersections

def test8_firstList : Array Interval := #[(-5,-3),(-1,2),(4,4)]
def test8_secondList : Array Interval := #[(-4,-2),(0,0),(3,5)]
def test8_Expected : Array Interval := #[(-4,-3),(0,0),(4,4)]

-- Test case 9: intersections where one interval from second overlaps two from first (due to disjointness, this can happen)

def test9_firstList : Array Interval := #[(0,1),(3,5),(7,9)]
def test9_secondList : Array Interval := #[(1,7)]
def test9_Expected : Array Interval := #[(1,1),(3,5),(7,7)]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((IntervalListIntersections test1_firstList test1_secondList).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((IntervalListIntersections test2_firstList test2_secondList).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((IntervalListIntersections test3_firstList test3_secondList).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((IntervalListIntersections test4_firstList test4_secondList).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((IntervalListIntersections test5_firstList test5_secondList).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((IntervalListIntersections test6_firstList test6_secondList).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((IntervalListIntersections test7_firstList test7_secondList).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((IntervalListIntersections test8_firstList test8_secondList).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((IntervalListIntersections test9_firstList test9_secondList).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test IntervalListIntersections (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

lemma array_getElem!_eq_getElem {α} [Inhabited α] (xs : Array α) (i : Nat) (h : i < xs.size) :
    xs[i]! = xs[i]'h := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, h]

lemma array_extract_zero_getElem! {α} [Inhabited α] (xs : Array α) (stop i : Nat)
    (hi : stop ≤ xs.size) (h : i < stop) :
    (xs.extract 0 stop)[i]! = xs[i]! := by
  have hsize : i < (xs.extract 0 stop).size := by
    simpa [Array.size_extract, Nat.min_eq_left hi, Nat.sub_zero] using h
  have hixs : i < xs.size := Nat.lt_of_lt_of_le h hi
  have hL : (xs.extract 0 stop)[i]! = (xs.extract 0 stop)[i]'hsize := by
    simpa using array_getElem!_eq_getElem (xs := xs.extract 0 stop) (i := i) hsize
  have hR : xs[i]! = xs[i]'hixs := by
    simpa using array_getElem!_eq_getElem (xs := xs) (i := i) hixs
  have hExtract : (xs.extract 0 stop)[i]'hsize = xs[0 + i]'(Array.getElem_extract_aux (xs := xs) (start := 0) (stop := stop) (i := i) hsize) := by
    simpa using (Array.getElem_extract (xs := xs) (start := 0) (stop := stop) (i := i) hsize)
  have hProofEq : (Array.getElem_extract_aux (xs := xs) (start := 0) (stop := stop) (i := i) hsize) = (by simpa using hixs : 0 + i < xs.size) := by
    apply Subsingleton.elim
  calc
    (xs.extract 0 stop)[i]! = (xs.extract 0 stop)[i]'hsize := hL
    _ = xs[0 + i]'(Array.getElem_extract_aux (xs := xs) (start := 0) (stop := stop) (i := i) hsize) := hExtract
    _ = xs[0 + i]'(by simpa using hixs : 0 + i < xs.size) := by simpa [hProofEq]
    _ = xs[i]'hixs := by
          -- remove the `0 +` in the index
          simp [Nat.zero_add]
    _ = xs[i]! := by
          simpa [hR]


theorem goal_0_0
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧
  (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧
    (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧
      (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧
        (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧
          ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} =
  {x |
        ∃ i_1,
          (i_1 < i ∧ i_1 < firstList.size) ∧
            (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩
      {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪
    {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
      {x |
        ∃ i,
          (i < j ∧ i < secondList.size) ∧
            (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    (i_1 : ℕ)
    : ∀ k < out.size, out[k]!.1 ≤ if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1 := by
  intro k hk
  have hx_valid : out[k]!.1 ≤ out[k]!.2 := by
    simpa using invariant_inv_out_valid k hk

  have hxL : out[k]!.1 ∈ {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} := by
    refine ⟨k, hk, ?_, ?_⟩
    · exact le_rfl
    · exact hx_valid

  have hxR : out[k]!.1 ∈
      ({x |
            ∃ i_1,
              (i_1 < i ∧ i_1 < firstList.size) ∧
                (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧
                  x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩
          {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪
        {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
          {x |
            ∃ i,
              (i < j ∧ i < secondList.size) ∧
                (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧
                  x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2}) := by
    simpa [invariant_inv_semantic] using hxL

  have hxR' := hxR
  simp [Set.mem_union, Set.mem_inter_iff] at hxR'
  rcases hxR' with h | h
  · rcases h with ⟨hA, hB⟩
    rcases hA with ⟨p, hp, hpL, hpR⟩
    rcases hp with ⟨hp_lt_i, hp_lt_size⟩

    have hEq : (firstList.extract 0 i)[p]! = firstList[p]! := by
      simpa using
        (array_extract_zero_getElem! (xs := firstList) (stop := i) (i := p) (hi := a) (h := hp_lt_i))

    have hx_le_firstEnd : out[k]!.1 ≤ firstList[p]!.2 := by
      simpa [hEq] using hpR

    have hfirstDisj : ∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1 :=
      require_1.2.2.2.2.1

    have hx_lt_firstStart : out[k]!.1 < firstList[i]!.1 :=
      lt_of_le_of_lt hx_le_firstEnd (hfirstDisj p i hp_lt_i a_2)

    have hfst_le_s : firstList[i]!.1 ≤
        (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) := by
      by_cases hcond : secondList[j]!.1 ≤ firstList[i]!.1
      · simp [hcond]
      · have : firstList[i]!.1 ≤ secondList[j]!.1 := le_of_lt (lt_of_not_ge hcond)
        simpa [hcond] using this

    exact le_trans (le_of_lt hx_lt_firstStart) hfst_le_s

  · rcases h with ⟨hC, hD⟩
    rcases hD with ⟨q, hq, hqL, hqR⟩
    rcases hq with ⟨hq_lt_j, hq_lt_size⟩

    have hEq : (secondList.extract 0 j)[q]! = secondList[q]! := by
      simpa using
        (array_extract_zero_getElem! (xs := secondList) (stop := j) (i := q) (hi := a_1) (h := hq_lt_j))

    have hx_le_secondEnd : out[k]!.1 ≤ secondList[q]!.2 := by
      simpa [hEq] using hqR

    have hsecondDisj : ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1 :=
      require_1.2.2.2.2.2

    have hx_lt_secondStart : out[k]!.1 < secondList[j]!.1 :=
      lt_of_le_of_lt hx_le_secondEnd (hsecondDisj q j hq_lt_j a_3)

    have hsec_le_s : secondList[j]!.1 ≤
        (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) := by
      by_cases hcond : secondList[j]!.1 ≤ firstList[i]!.1
      · simpa [hcond] using hcond
      · simp [hcond]

    exact le_trans (le_of_lt hx_lt_secondStart) hsec_le_s

theorem goal_0
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (if_pos_1 : firstList[i]!.2 < secondList[j]!.2)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    (if_pos : (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) ≤ if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2)
    : ∀ (i_1 j_1 : ℕ), i_1 < j_1 → j_1 < out.size + OfNat.ofNat 1 →
        (out.push
          (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1,
           if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.1 ≤
        (out.push
          (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1,
           if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[j_1]!.1 := by
  intro i_1 j_1 hij hj

  have hpush_lt : ∀ k < out.size,
      (out.push
        (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1,
         if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[k]! = out[k]! := by
    expose_names; intros; expose_names; try simp_all; try grind

  have hpush_last :
      (out.push
        (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1,
         if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[out.size]! =
        (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1,
         if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2) := by
    expose_names; intros; expose_names; try simp_all; try grind

  have hprev_start : ∀ k < out.size, out[k]!.1 ≤
      (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) := by
    expose_names; exact (goal_0_0 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid a_2 a_3 invariant_inv_semantic i_1)

  have hjle : j_1 ≤ out.size := by
    exact Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)

  rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
  · have hiout : i_1 < out.size := Nat.lt_trans hij hjlt
    have hsorted : out[i_1]!.1 ≤ out[j_1]!.1 := invariant_inv_out_sorted i_1 j_1 hij hjlt
    simpa [hpush_lt i_1 hiout, hpush_lt j_1 hjlt] using hsorted
  · subst hjeq
    have hiout : i_1 < out.size := Nat.lt_of_lt_of_le hij hjle
    have h := hprev_start i_1 hiout
    simpa [hpush_lt i_1 hiout, hpush_last] using h

namespace Array

lemma getElem!_extract_zero {α : Type} [Inhabited α]
    (xs : Array α) (n k : Nat) (hk : k < n) (hn : n ≤ xs.size) :
    (xs.extract 0 n)[k]! = xs[k]! := by
  have hkxs : k < xs.size := Nat.lt_of_lt_of_le hk hn
  have hkex : k < (xs.extract 0 n).size := by
    simpa [hn] using hk
  -- `simp` reduces the LHS to an `if k < n then xs[k] else default` form.
  simp [Array.getElem!_eq_getD, Array.getD, hkxs, hkex, hk]

end Array


theorem goal_1
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    : ∀ (i_1 j_1 : ℕ), i_1 < j_1 → j_1 < out.size + OfNat.ofNat 1 → (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.2 < (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[j_1]!.1 := by
  classical
  rcases require_1 with ⟨hValidF, hValidS, hSortF, hSortS, hDisF, hDisS⟩
  intro i1 j1 hij hj1

  set s : Int := (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1)
  set e : Int := (if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2)
  set newIv : Interval := (s, e)

  -- helper simplifications for `push`
  have push_get_lt {t : Nat} (ht : t < out.size) : (out.push newIv)[t]! = out[t]! := by
    have ht' : t < out.size + 1 := Nat.lt_add_one_of_le (Nat.le_of_lt ht)
    -- `simp` unfolds `getElem!` to `getD`, then uses `getElem_push`.
    simp [Array.getElem!_eq_getD, Array.getD, Array.size_push, ht', Array.getElem_push, ht, newIv]

  have push_get_size : (out.push newIv)[out.size]! = newIv := by
    have ht' : out.size < out.size + 1 := Nat.lt_add_one out.size
    simp [Array.getElem!_eq_getD, Array.getD, Array.size_push, ht', Array.getElem_push, newIv]

  have hjle : j1 ≤ out.size := by
    have : j1 < Nat.succ out.size := by
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj1
    exact Nat.lt_succ_iff.mp this

  rcases lt_or_eq_of_le hjle with hjlt | rfl
  · -- both indices are in the old `out`
    have hi1lt : i1 < out.size := Nat.lt_trans hij hjlt
    have hdis : out[i1]!.2 < out[j1]!.1 := invariant_inv_out_disjoint i1 j1 hij hjlt
    -- rewrite `push` accesses to old ones
    simpa [push_get_lt hi1lt, push_get_lt hjlt] using hdis

  · -- j1 = out.size, so right interval is the new one
    have hi1lt : i1 < out.size := by simpa using hij

    -- reduce goal to `out[i1]!.2 < s`
    have hgoal' : out[i1]!.2 < s := by
      have hsz : 0 < out.size := Nat.lt_of_le_of_lt (Nat.zero_le i1) hi1lt
      set last : Nat := out.size - 1
      have hlastlt : last < out.size := by
        have : Nat.pred out.size < out.size := Nat.pred_lt (Nat.ne_of_gt hsz)
        simpa [last, Nat.pred_eq_sub_one] using this
      have hi1le : i1 ≤ last := by
        have : i1 ≤ out.size - 1 := Nat.le_pred_of_lt hi1lt
        simpa [last] using this

      rcases lt_or_eq_of_le hi1le with hi1ltLast | hi1eqLast
      · -- i1 < last : compare to the last interval start, then bound by `s`
        have hdis : out[i1]!.2 < out[last]!.1 :=
          invariant_inv_out_disjoint i1 last hi1ltLast hlastlt
        have hstartLast : out[last]!.1 ≤ s := by
          -- use provided lemma `goal_0_0`
          have h :=
            goal_0_0 firstList secondList ⟨hValidF, hValidS, hSortF, hSortS, hDisF, hDisS⟩
              i j out a a_1 invariant_inv_out_valid a_2 a_3 invariant_inv_semantic i1
          exact h last hlastlt
        exact lt_of_lt_of_le hdis hstartLast

      · -- i1 = last : use semantic invariant to show the last old interval ends before `s`
        subst hi1eqLast
        have hvalidLast : out[last]!.1 ≤ out[last]!.2 := invariant_inv_out_valid last hlastlt
        let x : Int := out[last]!.2
        have hxL : x ∈ {x | ∃ t < out.size, out[t]!.1 ≤ x ∧ x ≤ out[t]!.2} := by
          refine ⟨last, hlastlt, ?_, ?_⟩
          · -- start ≤ end
            simpa [x] using hvalidLast
          · simp [x]

        have hxR : x ∈ ({x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract 0 i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 i)[i_1]!.2} ∩
          {x | ∃ t < secondList.size, secondList[t]!.1 ≤ x ∧ x ≤ secondList[t]!.2} ∪
          {x | ∃ t < firstList.size, firstList[t]!.1 ≤ x ∧ x ≤ firstList[t]!.2} ∩
          {x | ∃ t, (t < j ∧ t < secondList.size) ∧ (secondList.extract 0 j)[t]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[t]!.2}) := by
          simpa [invariant_inv_semantic] using hxL

        have hxlt : x < s := by
          rcases hxR with hxA | hxB
          · -- comes from firstList prefix < i
            rcases hxA.1 with ⟨p, hp, hpL, hpU⟩
            have hpi : p < i := hp.1
            have hend : firstList[p]!.2 < firstList[i]!.1 := hDisF p i hpi a_2
            have hp_ex_iv : (firstList.extract 0 i)[p]! = firstList[p]! :=
              Array.getElem!_extract_zero firstList i p hpi a
            have hp_ex : (firstList.extract 0 i)[p]!.2 = firstList[p]!.2 := by
              simpa using congrArg Prod.snd hp_ex_iv
            have hxle : x ≤ firstList[p]!.2 := by
              simpa [x, hp_ex] using hpU
            have hxlt_i1 : x < firstList[i]!.1 := lt_of_le_of_lt hxle hend
            have hle_s : firstList[i]!.1 ≤ s := by
              by_cases h : secondList[j]!.1 ≤ firstList[i]!.1
              · simp [s, h]
              · have : firstList[i]!.1 ≤ secondList[j]!.1 := le_of_not_ge h
                simp [s, h, this]
            exact lt_of_lt_of_le hxlt_i1 hle_s

          · -- comes from secondList prefix < j
            rcases hxB.2 with ⟨q, hq, hqL, hqU⟩
            have hqj : q < j := hq.1
            have hend : secondList[q]!.2 < secondList[j]!.1 := hDisS q j hqj a_3
            have hq_ex_iv : (secondList.extract 0 j)[q]! = secondList[q]! :=
              Array.getElem!_extract_zero secondList j q hqj a_1
            have hq_ex : (secondList.extract 0 j)[q]!.2 = secondList[q]!.2 := by
              simpa using congrArg Prod.snd hq_ex_iv
            have hxle : x ≤ secondList[q]!.2 := by
              simpa [x, hq_ex] using hqU
            have hxlt_j1 : x < secondList[j]!.1 := lt_of_le_of_lt hxle hend
            have hle_s : secondList[j]!.1 ≤ s := by
              by_cases h : secondList[j]!.1 ≤ firstList[i]!.1
              · simp [s, h]
              · simp [s, h]
            exact lt_of_lt_of_le hxlt_j1 hle_s

        simpa [x] using hxlt

    -- now rewrite pushed array indexing
    have : (out.push newIv)[i1]!.2 < (out.push newIv)[out.size]!.1 := by
      -- left is old element, right is newIv
      simpa [push_get_lt hi1lt, push_get_size, newIv, s] using hgoal'

    simpa [s, e, newIv] using this

namespace IntervalProofHelpers

open Classical

variable {α : Type} [Inhabited α]

lemma array_getBang_eq_getElem (xs : Array α) {i : Nat} (h : i < xs.size) :
    xs[i]! = xs[i]'h := by
  -- `simp` knows how to evaluate `get!` when index is in bounds
  simp [Array.get!_eq_getD_getElem?, h]

end IntervalProofHelpers

namespace IntervalProofHelpers

open Classical

variable {α : Type} [Inhabited α]

lemma array_getBang_push_lt (xs : Array α) (x : α) {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  have hp : i < (xs.push x).size := by
    simpa [Array.size_push] using Nat.lt_trans h (Nat.lt_succ_self xs.size)
  -- convert both get! into getElem using bounds
  have hL : (xs.push x)[i]! = (xs.push x)[i]'hp := IntervalProofHelpers.array_getBang_eq_getElem (xs := xs.push x) hp
  have hR : xs[i]! = xs[i]'h := IntervalProofHelpers.array_getBang_eq_getElem (xs := xs) h
  -- getElem commutes with push on old indices
  have hget : (xs.push x)[i]'hp = xs[i]'h := by
    simpa using (Array.getElem_push_lt (xs := xs) (x := x) (i := i) h)
  -- finish
  calc
    (xs.push x)[i]! = (xs.push x)[i]'hp := hL
    _ = xs[i]'h := hget
    _ = xs[i]! := by simpa [hR]

lemma array_getBang_push_eq (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  have hp : xs.size < (xs.push x).size := by
    simpa [Array.size_push] using Nat.lt_succ_self xs.size
  have hL : (xs.push x)[xs.size]! = (xs.push x)[xs.size]'hp :=
    IntervalProofHelpers.array_getBang_eq_getElem (xs := xs.push x) hp
  -- last index of push is the pushed element
  have hget : (xs.push x)[xs.size]'hp = x := by
    simpa using (Array.getElem_push_eq (xs := xs) (x := x))
  simpa [hL] using hget

end IntervalProofHelpers


theorem goal_2
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (if_pos_1 : firstList[i]!.2 < secondList[j]!.2)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    : {x | ∃ i_1 < out.size + OfNat.ofNat 1, (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.1 ≤ x ∧ x ≤ (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.2} = {x | ∃ i_1, (i_1 < i + OfNat.ofNat 1 ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2} := by
  classical
  rcases require_1 with ⟨hValid₁, hValid₂, hSort₁, hSort₂, hDis₁, hDis₂⟩
  set s : Int := if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1
  set e : Int := if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2
  set newIv : Interval := (s, e)

  have extract_first_eq (stop idx : Nat) (hstop : stop ≤ firstList.size) (hidx : idx < stop) :
      (firstList.extract 0 stop)[idx]! = firstList[idx]! := by
    have hsize : (firstList.extract 0 stop).size = stop := by
      simpa [Nat.sub_zero] using
        (Array.size_extract_of_le (i := 0) (j := stop) hstop : (firstList.extract 0 stop).size = stop - 0)
    have hidx' : idx < (firstList.extract 0 stop).size := by simpa [hsize] using hidx
    have hidxSz : idx < firstList.size := Nat.lt_of_lt_of_le hidx hstop
    have hb1 : (firstList.extract 0 stop)[idx]! = (firstList.extract 0 stop)[idx]'hidx' :=
      IntervalProofHelpers.array_getBang_eq_getElem (xs := firstList.extract 0 stop) hidx'
    have hb2 : firstList[idx]! = firstList[idx]'hidxSz :=
      IntervalProofHelpers.array_getBang_eq_getElem (xs := firstList) hidxSz
    have hb3 : (firstList.extract 0 stop)[idx]'hidx' = firstList[idx]'hidxSz := by
      simpa using (Array.getElem_extract (xs := firstList) (start := 0) (stop := stop) (i := idx) hidx')
    calc
      (firstList.extract 0 stop)[idx]! = (firstList.extract 0 stop)[idx]'hidx' := hb1
      _ = firstList[idx]'hidxSz := hb3
      _ = firstList[idx]! := by simpa [hb2]

  have extract_second_eq (stop idx : Nat) (hstop : stop ≤ secondList.size) (hidx : idx < stop) :
      (secondList.extract 0 stop)[idx]! = secondList[idx]! := by
    have hsize : (secondList.extract 0 stop).size = stop := by
      simpa [Nat.sub_zero] using
        (Array.size_extract_of_le (i := 0) (j := stop) hstop : (secondList.extract 0 stop).size = stop - 0)
    have hidx' : idx < (secondList.extract 0 stop).size := by simpa [hsize] using hidx
    have hidxSz : idx < secondList.size := Nat.lt_of_lt_of_le hidx hstop
    have hb1 : (secondList.extract 0 stop)[idx]! = (secondList.extract 0 stop)[idx]'hidx' :=
      IntervalProofHelpers.array_getBang_eq_getElem (xs := secondList.extract 0 stop) hidx'
    have hb2 : secondList[idx]! = secondList[idx]'hidxSz :=
      IntervalProofHelpers.array_getBang_eq_getElem (xs := secondList) hidxSz
    have hb3 : (secondList.extract 0 stop)[idx]'hidx' = secondList[idx]'hidxSz := by
      simpa using (Array.getElem_extract (xs := secondList) (start := 0) (stop := stop) (i := idx) hidx')
    calc
      (secondList.extract 0 stop)[idx]! = (secondList.extract 0 stop)[idx]'hidx' := hb1
      _ = secondList[idx]'hidxSz := hb3
      _ = secondList[idx]! := by simpa [hb2]

  have inv_mp {x : Int} :
      x ∈ {x | ∃ t < out.size, out[t]!.1 ≤ x ∧ x ≤ out[t]!.2} →
        x ∈ ({x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract 0 i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 i)[i_1]!.2} ∩
          {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪
        {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
          {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract 0 j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[i]!.2}) := by
    intro hx
    have hmem := congrArg (fun S => x ∈ S) invariant_inv_semantic
    exact hmem.mp hx

  have inv_mpr {x : Int} :
      x ∈ ({x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract 0 i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 i)[i_1]!.2} ∩
          {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪
        {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
          {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract 0 j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[i]!.2}) →
      x ∈ {x | ∃ t < out.size, out[t]!.1 ≤ x ∧ x ≤ out[t]!.2} := by
    intro hx
    have hmem := congrArg (fun S => x ∈ S) invariant_inv_semantic
    exact hmem.mpr hx

  ext x
  constructor
  · intro hx
    rcases hx with ⟨idx, hidx, hL, hR⟩
    have hidx' : idx < out.size + 1 := by simpa using hidx
    have hle : idx ≤ out.size := Nat.le_of_lt_succ hidx'
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · have hget : (out.push newIv)[idx]! = out[idx]! :=
        IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) hlt
      have hxOld : x ∈ {x | ∃ t < out.size, out[t]!.1 ≤ x ∧ x ≤ out[t]!.2} :=
        ⟨idx, hlt, by simpa [hget] using hL, by simpa [hget] using hR⟩
      have hxOldRhs := inv_mp (x := x) hxOld
      rcases (by simpa [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] using hxOldRhs) with
        hcase | hcase
      · rcases hcase with ⟨hPref, hSecAll⟩
        rcases hPref with ⟨i1, hi1, hiL, hiR⟩
        have hi1lt : i1 < i := hi1.1
        have hi1sz : i1 < firstList.size := hi1.2
        have hi1lt' : i1 < i + 1 := Nat.lt_trans hi1lt (Nat.lt_succ_self i)
        have hex_i : (firstList.extract 0 i)[i1]! = firstList[i1]! := extract_first_eq i i1 a hi1lt
        have hex_ip : (firstList.extract 0 (i+1))[i1]! = firstList[i1]! :=
          extract_first_eq (i+1) i1 (Nat.succ_le_of_lt a_2) hi1lt'
        have hiL' : (firstList.extract 0 (i+1))[i1]!.1 ≤ x := by simpa [hex_i, hex_ip] using hiL
        have hiR' : x ≤ (firstList.extract 0 (i+1))[i1]!.2 := by simpa [hex_i, hex_ip] using hiR
        have hxNewProp :
            ((∃ i_1,
                  (i_1 < i + 1 ∧ i_1 < firstList.size) ∧
                    (firstList.extract 0 (i + 1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 (i + 1))[i_1]!.2) ∧
                ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2) ∨
              (∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2) ∧
                ∃ i,
                  (i < j ∧ i < secondList.size) ∧
                    (secondList.extract 0 j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[i]!.2 := by
          refine Or.inl ?_
          refine ⟨?_, hSecAll⟩
          exact ⟨i1, ⟨hi1lt', hi1sz⟩, hiL', hiR'⟩
        exact (by simpa [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] using hxNewProp)
      · have hxNewProp :
            ((∃ i_1,
                  (i_1 < i + 1 ∧ i_1 < firstList.size) ∧
                    (firstList.extract 0 (i + 1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 (i + 1))[i_1]!.2) ∧
                ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2) ∨
              (∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2) ∧
                ∃ i,
                  (i < j ∧ i < secondList.size) ∧
                    (secondList.extract 0 j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[i]!.2 :=
          Or.inr hcase
        exact (by simpa [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] using hxNewProp)

    · -- idx = out.size
      have hget : (out.push newIv)[out.size]! = newIv :=
        IntervalProofHelpers.array_getBang_push_eq (xs := out) (x := newIv)
      have hL' : s ≤ x := by simpa [newIv, hget, s] using hL
      have hR' : x ≤ e := by simpa [newIv, hget, e] using hR
      have hle_end : firstList[i]!.2 ≤ secondList[j]!.2 := le_of_lt if_pos_1
      have hx_end : x ≤ firstList[i]!.2 := by simpa [e, hle_end] using hR'
      have hb_end : x ≤ secondList[j]!.2 := le_trans hx_end (le_of_lt if_pos_1)
      have ha_start : firstList[i]!.1 ≤ x := by
        by_cases hsj : secondList[j]!.1 ≤ firstList[i]!.1
        · have : s = firstList[i]!.1 := by simp [s, hsj]
          simpa [this] using hL'
        · have hb : secondList[j]!.1 ≤ x := by simpa [s, hsj] using hL'
          have ha_lt : firstList[i]!.1 < secondList[j]!.1 := lt_of_not_ge hsj
          exact le_trans (le_of_lt ha_lt) hb
      have hb_start : secondList[j]!.1 ≤ x := by
        by_cases hsj : secondList[j]!.1 ≤ firstList[i]!.1
        · have ha : firstList[i]!.1 ≤ x := by
            have : s = firstList[i]!.1 := by simp [s, hsj]
            simpa [this] using hL'
          exact le_trans hsj ha
        · simpa [s, hsj] using hL'
      have hxPref : x ∈ {x | ∃ i_1, (i_1 < i + 1 ∧ i_1 < firstList.size) ∧ (firstList.extract 0 (i+1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 (i+1))[i_1]!.2} := by
        have hex_ip : (firstList.extract 0 (i+1))[i]! = firstList[i]! :=
          extract_first_eq (i+1) i (Nat.succ_le_of_lt a_2) (Nat.lt_succ_self i)
        refine ⟨i, ⟨Nat.lt_succ_self i, a_2⟩, ?_, ?_⟩
        · simpa [hex_ip] using ha_start
        · simpa [hex_ip] using hx_end
      have hxSec : x ∈ {x | ∃ k < secondList.size, secondList[k]!.1 ≤ x ∧ x ≤ secondList[k]!.2} :=
        ⟨j, a_3, hb_start, hb_end⟩
      have : x ∈ ({x | ∃ i_1, (i_1 < i + 1 ∧ i_1 < firstList.size) ∧ (firstList.extract 0 (i+1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 (i+1))[i_1]!.2} ∩
          {x | ∃ k < secondList.size, secondList[k]!.1 ≤ x ∧ x ≤ secondList[k]!.2}) := ⟨hxPref, hxSec⟩
      simpa [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] using (Or.inl this)

  · intro hx
    rcases (by simpa [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] using hx) with
      hxLeft | hxRight
    · rcases hxLeft with ⟨hxPref, hxSecAll⟩
      rcases hxPref with ⟨i1, hi1, hiL, hiR⟩
      rcases hxSecAll with ⟨k, hk, hkL, hkR⟩
      have hi1le : i1 ≤ i := Nat.le_of_lt_succ (by simpa using hi1.1)
      rcases Nat.lt_or_eq_of_le hi1le with hi1lt | hi1eq
      · -- i1 < i
        have hex_i : (firstList.extract 0 i)[i1]! = firstList[i1]! := extract_first_eq i i1 a hi1lt
        have hex_ip : (firstList.extract 0 (i+1))[i1]! = firstList[i1]! :=
          extract_first_eq (i+1) i1 (Nat.succ_le_of_lt a_2) hi1.1
        have hiL' : (firstList.extract 0 i)[i1]!.1 ≤ x := by simpa [hex_i, hex_ip] using hiL
        have hiR' : x ≤ (firstList.extract 0 i)[i1]!.2 := by simpa [hex_i, hex_ip] using hiR
        have hxOldRhs : x ∈ ({x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract 0 i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 i)[i_1]!.2} ∩
            {x | ∃ k < secondList.size, secondList[k]!.1 ≤ x ∧ x ≤ secondList[k]!.2} ∪
          {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
            {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract 0 j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[i]!.2}) := by
          refine Or.inl ⟨?_, ⟨k, hk, hkL, hkR⟩⟩
          exact ⟨i1, ⟨hi1lt, hi1.2⟩, hiL', hiR'⟩
        have hxOldOut := inv_mpr (x := x) hxOldRhs
        rcases hxOldOut with ⟨t, ht, htL, htR⟩
        refine ⟨t, Nat.lt_trans ht (Nat.lt_succ_self out.size), ?_, ?_⟩
        · have hget : (out.push newIv)[t]! = out[t]! :=
            IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) ht
          simpa [hget] using htL
        · have hget : (out.push newIv)[t]! = out[t]! :=
            IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) ht
          simpa [hget] using htR
      · -- i1 = i
        have hiL' : (firstList.extract 0 (i+1))[i]!.1 ≤ x := by simpa [hi1eq] using hiL
        have hiR' : x ≤ (firstList.extract 0 (i+1))[i]!.2 := by simpa [hi1eq] using hiR
        have hex_ip : (firstList.extract 0 (i+1))[i]! = firstList[i]! :=
          extract_first_eq (i+1) i (Nat.succ_le_of_lt a_2) (Nat.lt_succ_self i)
        have ha_start : firstList[i]!.1 ≤ x := by simpa [hex_ip] using hiL'
        have ha_end : x ≤ firstList[i]!.2 := by simpa [hex_ip] using hiR'
        have hk_cases : k < j ∨ k = j ∨ j < k := lt_trichotomy k j
        rcases hk_cases with hklt | hkeq | hkgt
        · -- k < j
          have hxAllFirst : x ∈ {x | ∃ t < firstList.size, firstList[t]!.1 ≤ x ∧ x ≤ firstList[t]!.2} :=
            ⟨i, a_2, ha_start, ha_end⟩
          have hex_sec : (secondList.extract 0 j)[k]! = secondList[k]! :=
            extract_second_eq j k a_1 hklt
          have hkL' : (secondList.extract 0 j)[k]!.1 ≤ x := by simpa [hex_sec] using hkL
          have hkR' : x ≤ (secondList.extract 0 j)[k]!.2 := by simpa [hex_sec] using hkR
          have hxPrefSecond : x ∈ {x | ∃ k, (k < j ∧ k < secondList.size) ∧ (secondList.extract 0 j)[k]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[k]!.2} :=
            ⟨k, ⟨hklt, hk⟩, hkL', hkR'⟩
          have hxOldRhs : x ∈ ({x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract 0 i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 i)[i_1]!.2} ∩
              {x | ∃ k < secondList.size, secondList[k]!.1 ≤ x ∧ x ≤ secondList[k]!.2} ∪
            {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
              {x | ∃ k, (k < j ∧ k < secondList.size) ∧ (secondList.extract 0 j)[k]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[k]!.2}) :=
            Or.inr ⟨hxAllFirst, hxPrefSecond⟩
          have hxOldOut := inv_mpr (x := x) hxOldRhs
          rcases hxOldOut with ⟨t, ht, htL, htR⟩
          refine ⟨t, Nat.lt_trans ht (Nat.lt_succ_self out.size), ?_, ?_⟩
          · have hget : (out.push newIv)[t]! = out[t]! :=
              IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) ht
            simpa [hget] using htL
          · have hget : (out.push newIv)[t]! = out[t]! :=
              IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) ht
            simpa [hget] using htR
        · -- k = j
          have hkL' : secondList[j]!.1 ≤ x := by simpa [hkeq] using hkL
          have hpushLast : (out.push newIv)[out.size]! = newIv :=
            IntervalProofHelpers.array_getBang_push_eq (xs := out) (x := newIv)
          refine ⟨out.size, Nat.lt_succ_self out.size, ?_, ?_⟩
          · -- start
            have : newIv.1 ≤ x := by
              by_cases hsj : secondList[j]!.1 ≤ firstList[i]!.1
              · have hs : newIv.1 = firstList[i]!.1 := by simp [newIv, s, hsj]
                simpa [hs] using ha_start
              · have hs : newIv.1 = secondList[j]!.1 := by simp [newIv, s, hsj]
                simpa [hs] using hkL'
            simpa [hpushLast] using this
          · -- end
            have hle_end : firstList[i]!.2 ≤ secondList[j]!.2 := le_of_lt if_pos_1
            have he : newIv.2 = firstList[i]!.2 := by simp [newIv, e, hle_end]
            have : x ≤ newIv.2 := by simpa [he] using ha_end
            simpa [hpushLast] using this
        · -- j < k
          have hdis : secondList[j]!.2 < secondList[k]!.1 := hDis₂ j k hkgt hk
          have x_le_jend : x ≤ secondList[j]!.2 := le_trans ha_end (le_of_lt if_pos_1)
          have : x < secondList[k]!.1 := lt_of_le_of_lt x_le_jend hdis
          exact (False.elim ((not_lt_of_ge hkL) this))

    · -- unchanged right component
      rcases hxRight with ⟨hxAllFirst, hxPrefSecond⟩
      have hxOldRhs : x ∈ ({x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract 0 i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract 0 i)[i_1]!.2} ∩
          {x | ∃ k < secondList.size, secondList[k]!.1 ≤ x ∧ x ≤ secondList[k]!.2} ∪
        {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩
          {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract 0 j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract 0 j)[i]!.2}) :=
        Or.inr ⟨hxAllFirst, hxPrefSecond⟩
      have hxOldOut := inv_mpr (x := x) hxOldRhs
      rcases hxOldOut with ⟨t, ht, htL, htR⟩
      refine ⟨t, Nat.lt_trans ht (Nat.lt_succ_self out.size), ?_, ?_⟩
      · have hget : (out.push newIv)[t]! = out[t]! :=
          IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) ht
        simpa [hget] using htL
      · have hget : (out.push newIv)[t]! = out[t]! :=
          IntervalProofHelpers.array_getBang_push_lt (xs := out) (x := newIv) ht
        simpa [hget] using htR

theorem goal_3
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    : ∀ (i_1 j_1 : ℕ), i_1 < j_1 → j_1 < out.size + OfNat.ofNat 1 → (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.1 ≤ (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[j_1]!.1 := by
  classical
  intro i_1 j_1 hij hj_1

  set newIv : Interval :=
    (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1,
      if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2)

  -- helper rewrites for getElem! over push
  have push_getBang_lt {k : Nat} (hk : k < out.size) : (out.push newIv)[k]! = out[k]! := by
    have hk' : k < (out.push newIv).size := by
      have : k < out.size.succ := Nat.lt_trans hk (Nat.lt_succ_self out.size)
      simpa [Array.size_push, Nat.succ_eq_add_one] using this
    -- `simp` reduces the in-bounds branch; we then discharge the impossible out-of-bounds branch
    simp [Array.getElem!_eq_getD, Array.getD, hk, hk', Array.getElem_push, newIv]
    intro hkge
    have hk'' : k < out.size + 1 := by
      simpa [Array.size_push] using hk'
    exfalso
    exact Nat.not_le_of_lt hk'' hkge

  have push_getBang_eq : (out.push newIv)[out.size]! = newIv := by
    have hs : out.size < (out.push newIv).size := by
      have : out.size < out.size.succ := Nat.lt_succ_self out.size
      simpa [Array.size_push, Nat.succ_eq_add_one] using this
    simp [Array.getElem!_eq_getD, Array.getD, hs, Array.getElem_push, newIv]

  have hj_1' : j_1 < out.size.succ := by
    simpa [Nat.succ_eq_add_one] using hj_1
  have hj_1le : j_1 ≤ out.size := (Nat.lt_succ_iff.mp hj_1')
  cases lt_or_eq_of_le hj_1le with
  | inl hjlt =>
      have hi_1lt : i_1 < out.size := Nat.lt_trans hij hjlt
      have hsorted : out[i_1]!.1 ≤ out[j_1]!.1 := invariant_inv_out_sorted i_1 j_1 hij hjlt
      simpa [newIv, push_getBang_lt hi_1lt, push_getBang_lt hjlt] using hsorted
  | inr hjeq =>
      have hi_1lt : i_1 < out.size := by
        simpa [hjeq] using hij
      have hstartFun :=
        goal_0_0 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid a_2 a_3
          invariant_inv_semantic i_1
      have hstart : out[i_1]!.1 ≤ (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) :=
        hstartFun i_1 hi_1lt
      simpa [newIv, hjeq, push_getBang_lt hi_1lt, push_getBang_eq] using hstart

theorem goal_4
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    : ∀ (i_1 j_1 : ℕ), i_1 < j_1 → j_1 < out.size + OfNat.ofNat 1 → (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.2 < (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[j_1]!.1 := by
    intros; expose_names; exact
        goal_1 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid
          invariant_inv_out_disjoint a_2 a_3 invariant_inv_semantic i_1 j_1 h h_1



theorem goal_5
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    (if_pos : (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1) ≤ if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2)
    (if_neg : secondList[j]!.2 ≤ firstList[i]!.2)
    : {x | ∃ i_1 < out.size + OfNat.ofNat 1, (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.1 ≤ x ∧ x ≤ (out.push (if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1, if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2))[i_1]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j + OfNat.ofNat 1 ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.2} := by
    sorry

theorem goal_6
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (if_pos : firstList[i]!.2 < secondList[j]!.2)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    (if_neg : (if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2) < if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1)
    : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i + OfNat.ofNat 1 ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2} := by
    sorry

theorem goal_7
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i : ℕ)
    (j : ℕ)
    (out : Array Interval)
    (a : i ≤ firstList.size)
    (a_1 : j ≤ secondList.size)
    (invariant_inv_out_valid : ∀ k < out.size, out[k]!.1 ≤ out[k]!.2)
    (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.1 ≤ out[j]!.1)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out.size → out[i]!.2 < out[j]!.1)
    (a_2 : i < firstList.size)
    (a_3 : j < secondList.size)
    (invariant_inv_semantic : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) j)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) j)[i]!.2})
    (if_neg : (if firstList[i]!.2 ≤ secondList[j]!.2 then firstList[i]!.2 else secondList[j]!.2) < if secondList[j]!.1 ≤ firstList[i]!.1 then firstList[i]!.1 else secondList[j]!.1)
    (if_neg_1 : secondList[j]!.2 ≤ firstList[i]!.2)
    : {x | ∃ i < out.size, out[i]!.1 ≤ x ∧ x ≤ out[i]!.2} = {x | ∃ i_1, (i_1 < i ∧ i_1 < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i)[i_1]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < j + OfNat.ofNat 1 ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) (j + OfNat.ofNat 1))[i]!.2} := by
    sorry

theorem goal_8
    (firstList : Array Interval)
    (secondList : Array Interval)
    (require_1 : (∀ i < firstList.size, firstList[i]!.1 ≤ firstList[i]!.2) ∧ (∀ i < secondList.size, secondList[i]!.1 ≤ secondList[i]!.2) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.1 ≤ firstList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.1 ≤ secondList[j]!.1) ∧ (∀ (i j : ℕ), i < j → j < firstList.size → firstList[i]!.2 < firstList[j]!.1) ∧ ∀ (i j : ℕ), i < j → j < secondList.size → secondList[i]!.2 < secondList[j]!.1)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (out_1 : Array Interval)
    (a : i_1 ≤ firstList.size)
    (a_1 : i_2 ≤ secondList.size)
    (done_1 : i_1 = firstList.size ∨ i_2 = secondList.size)
    (invariant_inv_out_valid : ∀ k < out_1.size, out_1[k]!.1 ≤ out_1[k]!.2)
    (invariant_inv_out_sorted : ∀ (i j : ℕ), i < j → j < out_1.size → out_1[i]!.1 ≤ out_1[j]!.1)
    (invariant_inv_out_disjoint : ∀ (i j : ℕ), i < j → j < out_1.size → out_1[i]!.2 < out_1[j]!.1)
    (invariant_inv_semantic : {x | ∃ i < out_1.size, out_1[i]!.1 ≤ x ∧ x ≤ out_1[i]!.2} = {x | ∃ i, (i < i_1 ∧ i < firstList.size) ∧ (firstList.extract (OfNat.ofNat 0) i_1)[i]!.1 ≤ x ∧ x ≤ (firstList.extract (OfNat.ofNat 0) i_1)[i]!.2} ∩ {x | ∃ i < secondList.size, secondList[i]!.1 ≤ x ∧ x ≤ secondList[i]!.2} ∪ {x | ∃ i < firstList.size, firstList[i]!.1 ≤ x ∧ x ≤ firstList[i]!.2} ∩ {x | ∃ i, (i < i_2 ∧ i < secondList.size) ∧ (secondList.extract (OfNat.ofNat 0) i_2)[i]!.1 ≤ x ∧ x ≤ (secondList.extract (OfNat.ofNat 0) i_2)[i]!.2})
    : postcondition firstList secondList out_1 := by
    sorry


set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 4)))


prove_correct IntervalListIntersections by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_disjoint a_2 a_3 if_pos_1 invariant_inv_semantic if_pos)
  exact (goal_1 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_disjoint a_2 a_3 invariant_inv_semantic)
  exact (goal_2 firstList secondList require_1 i j out a a_1 a_2 a_3 if_pos_1 invariant_inv_semantic)
  exact (goal_3 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_sorted a_2 a_3 invariant_inv_semantic)
  exact (goal_4 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_disjoint a_2 a_3 invariant_inv_semantic)
  exact (goal_5 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_disjoint a_2 a_3 invariant_inv_semantic if_pos if_neg)
  exact (goal_6 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_disjoint a_2 a_3 if_pos invariant_inv_semantic if_neg)
  exact (goal_7 firstList secondList require_1 i j out a a_1 invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_disjoint a_2 a_3 invariant_inv_semantic if_neg if_neg_1)
  exact (goal_8 firstList secondList require_1 i_1 i_2 out_1 a a_1 done_1 invariant_inv_out_valid invariant_inv_out_sorted invariant_inv_out_disjoint invariant_inv_semantic)
end Proof
