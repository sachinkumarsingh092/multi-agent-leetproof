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
def helper (a : Array Interval) (b : Array Interval) (i : Nat) (j : Nat) (acc : Array Interval) : Array Interval :=
  if hi : i < a.size then
    if hj : j < b.size then
      let ai := a[i]
      let bj := b[j]
      let lo := max ai.1 bj.1
      let hi' := min ai.2 bj.2
      let acc' := if lo ≤ hi' then acc.push (lo, hi') else acc
      if ai.2 ≤ bj.2 then
        helper a b (i + 1) j acc'
      else
        helper a b i (j + 1) acc'
    else acc
  else acc
termination_by a.size - i + b.size - j

def implementation (firstList : Array Interval) (secondList : Array Interval) : Array Interval :=
  helper firstList secondList 0 0 #[]
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
#assert_same_evaluation #[(implementation test1_firstList test1_secondList), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_firstList test2_secondList), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_firstList test3_secondList), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_firstList test4_secondList), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_firstList test5_secondList), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_firstList test6_secondList), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_firstList test7_secondList), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_firstList test8_secondList), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_firstList test9_secondList), test9_Expected]
end Assertions

section Pbt
method implementationPbt (firstList : Array Interval) (secondList : Array Interval)
  return (result : Array Interval)
  require precondition firstList secondList
  ensures postcondition firstList secondList result
  do
  return (implementation firstList secondList)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
lemma acc_push_valid (acc : Array Interval) (iv : Interval) (h_acc : ∀ k < acc.size, isValidInterval acc[k]!) (h_iv : isValidInterval iv) :
    ∀ k < (acc.push iv).size, isValidInterval (acc.push iv)[k]! := by
  intro k hk
  simp only [Array.size_push] at hk
  by_cases hlt : k < acc.size
  · have hlt2 : k < (acc.push iv).size := by simp [Array.size_push]; omega
    have h1 : (acc.push iv)[k]! = acc[k]! := by
      simp only [Array.getElem!_eq_getD, Array.getD, hlt2, hlt, dite_true,
        Array.getInternal_eq_getElem, Array.getElem_push_lt hlt]
    rw [h1]
    exact h_acc k hlt
  · have hk_eq : k = acc.size := by omega
    subst hk_eq
    have hlt2 : acc.size < (acc.push iv).size := by simp [Array.size_push]
    have h2 : (acc.push iv)[acc.size]! = iv := by
      simp only [Array.getElem!_eq_getD, Array.getD, hlt2, dite_true,
        Array.getInternal_eq_getElem, Array.getElem_push]
      simp
    rw [h2]
    exact h_iv


theorem correctness_goal_0_0 : ∀ (a b : Array Interval) (i j : ℕ) (acc : Array Interval),
  (∀ k < acc.size, isValidInterval acc[k]!) → ∀ k < (helper a b i j acc).size, isValidInterval (helper a b i j acc)[k]! := by
    intro a b
    suffices h : ∀ (n : ℕ) (i j : ℕ), a.size - i + b.size - j ≤ n →
      ∀ (acc : Array Interval), (∀ k < acc.size, isValidInterval acc[k]!) →
        ∀ k < (helper a b i j acc).size, isValidInterval (helper a b i j acc)[k]! by
      intro i j acc hacc
      exact h (a.size - i + b.size - j) i j (le_refl _) acc hacc
    intro n
    induction n with
    | zero =>
      intro i j hle acc hacc
      unfold helper
      split
      · rename_i hi
        split
        · rename_i hj; omega
        · exact hacc
      · exact hacc
    | succ n ih =>
      intro i j hle acc hacc
      unfold helper
      split
      · rename_i hi
        split
        · rename_i hj
          -- reduce the let bindings
          dsimp only []
          have h_acc' : ∀ k < (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc).size,
            isValidInterval (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc)[k]! := by
            split
            · rename_i hlo
              apply acc_push_valid
              · exact hacc
              · exact hlo
            · exact hacc
          split
          · apply ih (i + 1) j _ _ h_acc'; omega
          · apply ih i (j + 1) _ _ h_acc'; omega
        · exact hacc
      · exact hacc

theorem correctness_goal_0
    (firstList : Array Interval)
    (secondList : Array Interval)
    : ∀ k < (implementation firstList secondList).size, isValidInterval (implementation firstList secondList)[k]! := by
    have h_helper : ∀ (a b : Array Interval) (i j : Nat) (acc : Array Interval),
      (∀ k < acc.size, isValidInterval acc[k]!) →
      ∀ k < (helper a b i j acc).size, isValidInterval (helper a b i j acc)[k]! := by expose_names; exact (correctness_goal_0_0)
    unfold implementation
    exact h_helper firstList secondList 0 0 #[] (by intro k hk; simp [Array.size] at hk)

lemma sortedByStart_push (acc : Array Interval) (iv : Interval)
    (h_sorted : sortedByStart acc)
    (h_last : acc.size > 0 → acc[acc.size - 1]!.1 ≤ iv.1) :
    sortedByStart (acc.push iv) := by
  unfold sortedByStart at *
  intro p q hpq hq_lt
  rw [Array.size_push] at hq_lt
  have hp_lt : p < acc.size := by omega
  by_cases hq_eq : q = acc.size
  · subst hq_eq
    have h_pos : acc.size > 0 := by omega
    have hp_push : (acc.push iv)[p]! = acc[p]! := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?, Array.size_push, hp_lt,
            Array.getElem?_push_lt hp_lt]
    have hq_push : (acc.push iv)[acc.size]! = iv := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?, Array.size_push,
            show acc.size < acc.size + 1 from by omega]
    rw [hp_push, hq_push]
    by_cases hp_eq : p = acc.size - 1
    · subst hp_eq; exact h_last h_pos
    · calc acc[p]!.1 ≤ acc[acc.size - 1]!.1 := h_sorted p (acc.size - 1) (by omega) (by omega)
           _ ≤ iv.1 := h_last h_pos
  · have hq_lt' : q < acc.size := by omega
    have hp_push : (acc.push iv)[p]! = acc[p]! := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?, Array.size_push, hp_lt,
            Array.getElem?_push_lt hp_lt]
    have hq_push : (acc.push iv)[q]! = acc[q]! := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?, Array.size_push, hq_lt',
            Array.getElem?_push_lt hq_lt']
    rw [hp_push, hq_push]
    exact h_sorted p q hpq hq_lt'

lemma push_last_eq (acc : Array Interval) (iv : Interval) :
    (acc.push iv)[(acc.push iv).size - 1]! = iv := by
  simp [Array.size_push, show acc.size + 1 - 1 = acc.size from by omega]


theorem correctness_goal_1_0 : ∀ (a b : Array Interval) (i j : ℕ) (acc : Array Interval),
  sortedByStart a →
    sortedByStart b →
      pairwiseDisjointClosed a →
        pairwiseDisjointClosed b →
          (∀ k < a.size, isValidInterval a[k]!) →
            (∀ k < b.size, isValidInterval b[k]!) →
              sortedByStart acc →
                (acc.size > 0 → i < a.size → j < b.size → acc[acc.size - 1]!.1 ≤ max a[i]!.1 b[j]!.1) →
                  sortedByStart (helper a b i j acc) := by
    intro a b
    suffices ∀ (fuel : ℕ), ∀ (i j : ℕ),
      a.size - i + b.size - j ≤ fuel →
      ∀ (acc : Array Interval),
        sortedByStart a → sortedByStart b → pairwiseDisjointClosed a → pairwiseDisjointClosed b →
        (∀ k < a.size, isValidInterval a[k]!) → (∀ k < b.size, isValidInterval b[k]!) →
        sortedByStart acc →
        (acc.size > 0 → i < a.size → j < b.size → acc[acc.size - 1]!.1 ≤ max a[i]!.1 b[j]!.1) →
        sortedByStart (helper a b i j acc) by
      intro i j acc h_sa h_sb h_da h_db h_va h_vb h_sacc h_inv
      exact this (a.size - i + b.size - j) i j le_rfl acc h_sa h_sb h_da h_db h_va h_vb h_sacc h_inv
    intro fuel
    induction fuel with
    | zero =>
      intro i j h_fuel acc h_sa h_sb h_da h_db h_va h_vb h_sacc h_inv
      unfold helper
      split
      · rename_i hi
        split
        · rename_i hj; omega
        · exact h_sacc
      · exact h_sacc
    | succ fuel' ih_fuel =>
      intro i j h_fuel acc h_sa h_sb h_da h_db h_va h_vb h_sacc h_inv
      unfold helper
      split
      · rename_i hi
        split
        · rename_i hj
          dsimp only []
          have h_ai_eq : a[i] = a[i]! := by
            simp [Array.getElem!_eq_getD, Array.getD_getElem?, hi]
          have h_bj_eq : b[j] = b[j]! := by
            simp [Array.getElem!_eq_getD, Array.getD_getElem?, hj]
          set acc' := if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc with hacc'_def
          have h_acc'_sorted : sortedByStart acc' := by
            simp only [hacc'_def]
            split
            · apply sortedByStart_push _ _ h_sacc
              intro h_pos
              rw [h_ai_eq, h_bj_eq]
              exact h_inv h_pos hi hj
            · exact h_sacc
          split
          · -- a[i].2 ≤ b[j].2, recurse (i+1, j)
            apply ih_fuel (i + 1) j (by omega) acc'
            · exact h_sa
            · exact h_sb
            · exact h_da
            · exact h_db
            · exact h_va
            · exact h_vb
            · exact h_acc'_sorted
            · intro h_pos' hi' hj'
              have h_mono : a[i]!.1 ≤ a[i+1]!.1 := h_sa i (i+1) (by omega) hi'
              have h_max_mono : max a[i]!.1 b[j]!.1 ≤ max a[i+1]!.1 b[j]!.1 :=
                max_le_max_right _ h_mono
              simp only [hacc'_def]
              split
              · rw [push_last_eq]
                show max a[i].1 b[j].1 ≤ max a[i+1]!.1 b[j]!.1
                rw [h_ai_eq, h_bj_eq]
                exact h_max_mono
              · rename_i h_no_push
                have h_pos : acc.size > 0 := by
                  simp [hacc'_def, h_no_push] at h_pos'; exact h_pos'
                calc acc[acc.size - 1]!.1 ≤ max a[i]!.1 b[j]!.1 := h_inv h_pos hi hj
                     _ ≤ max a[i+1]!.1 b[j]!.1 := h_max_mono
          · -- a[i].2 > b[j].2, recurse (i, j+1)
            apply ih_fuel i (j + 1) (by omega) acc'
            · exact h_sa
            · exact h_sb
            · exact h_da
            · exact h_db
            · exact h_va
            · exact h_vb
            · exact h_acc'_sorted
            · intro h_pos' hi' hj'
              have h_mono : b[j]!.1 ≤ b[j+1]!.1 := h_sb j (j+1) (by omega) hj'
              have h_max_mono : max a[i]!.1 b[j]!.1 ≤ max a[i]!.1 b[j+1]!.1 :=
                max_le_max_left _ h_mono
              simp only [hacc'_def]
              split
              · rw [push_last_eq]
                show max a[i].1 b[j].1 ≤ max a[i]!.1 b[j+1]!.1
                rw [h_ai_eq, h_bj_eq]
                exact h_max_mono
              · rename_i h_not_le h_no_push
                have h_pos : acc.size > 0 := by
                  simp [hacc'_def, h_no_push] at h_pos'; exact h_pos'
                calc acc[acc.size - 1]!.1 ≤ max a[i]!.1 b[j]!.1 := h_inv h_pos hi hj
                     _ ≤ max a[i]!.1 b[j+1]!.1 := h_max_mono
        · exact h_sacc
      · exact h_sacc

theorem correctness_goal_1
    (firstList : Array Interval)
    (secondList : Array Interval)
    (h_precond : precondition firstList secondList)
    : sortedByStart (implementation firstList secondList) := by
    unfold implementation
    have h_main : ∀ (a b : Array Interval) (i j : Nat) (acc : Array Interval),
      sortedByStart a → sortedByStart b →
      pairwiseDisjointClosed a → pairwiseDisjointClosed b →
      (∀ k < a.size, isValidInterval a[k]!) →
      (∀ k < b.size, isValidInterval b[k]!) →
      sortedByStart acc →
      (acc.size > 0 → i < a.size → j < b.size → acc[acc.size - 1]!.1 ≤ max a[i]!.1 b[j]!.1) →
      sortedByStart (helper a b i j acc) := by expose_names; exact (correctness_goal_1_0)
    exact h_main firstList secondList 0 0 #[]
      h_precond.2.2.1 h_precond.2.2.2.1
      h_precond.2.2.2.2.1 h_precond.2.2.2.2.2
      h_precond.1 h_precond.2.1
      (by intro i j _ hj; exact absurd hj (by simp [Array.size]))
      (by intro h; exact absurd h (by simp [Array.size]))


lemma pairwiseDisjointClosed_push (acc : Array Interval) (iv : Interval)
    (h_disj : pairwiseDisjointClosed acc)
    (h_valid : ∀ k < acc.size, isValidInterval acc[k]!)
    (h_gap : acc.size > 0 → acc[acc.size - 1]!.2 < iv.1) :
    pairwiseDisjointClosed (acc.push iv) := by
  unfold pairwiseDisjointClosed at *
  intro i j hij hjsize
  rw [Array.size_push] at hjsize
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at *
  by_cases hj_lt : j < acc.size
  · -- both i, j index into acc
    have hi_lt : i < acc.size := Nat.lt_trans hij hj_lt
    have h := h_disj i j hij hj_lt
    rw [Array.getElem?_eq_getElem hi_lt] at h
    rw [Array.getElem?_eq_getElem hj_lt] at h
    simp at h
    rw [Array.getElem?_push_lt hi_lt, Array.getElem?_push_lt hj_lt]
    simpa
  · -- j = acc.size (the new element)
    have hj_eq : j = acc.size := by omega
    subst hj_eq
    have hi_lt : i < acc.size := by omega
    have hacc_pos : acc.size > 0 := by omega
    rw [Array.getElem?_push_lt hi_lt, Array.getElem?_push_size]
    simp
    -- Goal: acc[i].2 < iv.1
    by_cases hi_last : i = acc.size - 1
    · subst hi_last
      have h3 := h_gap hacc_pos
      rw [Array.getElem?_eq_getElem (by omega)] at h3
      simpa using h3
    · have hlast : acc.size - 1 < acc.size := by omega
      have h1 := h_disj i (acc.size - 1) (by omega) (by omega)
      have h2 := h_valid (acc.size - 1) hlast
      unfold isValidInterval at h2
      have h3 := h_gap hacc_pos
      rw [Array.getElem?_eq_getElem hi_lt] at h1
      rw [Array.getElem?_eq_getElem hlast] at h1 h2 h3
      simp at h1 h2 h3
      linarith



lemma helper_pairwiseDisjoint (a b : Array Interval) (i j : ℕ) (acc : Array Interval)
    (h_sa : sortedByStart a)
    (h_sb : sortedByStart b)
    (h_da : pairwiseDisjointClosed a)
    (h_db : pairwiseDisjointClosed b)
    (h_va : ∀ k < a.size, isValidInterval a[k]!)
    (h_vb : ∀ k < b.size, isValidInterval b[k]!)
    (h_dacc : pairwiseDisjointClosed acc)
    (h_vacc : ∀ k < acc.size, isValidInterval acc[k]!)
    (h_gap : acc.size > 0 → i < a.size → j < b.size → acc[acc.size - 1]!.2 < max a[i]!.1 b[j]!.1) :
    pairwiseDisjointClosed (helper a b i j acc) := by
  unfold helper
  split
  · rename_i hi
    split
    · rename_i hj
      have ai_eq : a[i]! = a[i] := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      have bj_eq : b[j]! = b[j] := by
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
      show pairwiseDisjointClosed
        (if a[i].2 ≤ b[j].2 then
          helper a b (i + 1) j (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc)
        else
          helper a b i (j + 1) (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc))
      have h_dacc' : pairwiseDisjointClosed (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc) := by
        split
        · apply pairwiseDisjointClosed_push _ _ h_dacc h_vacc
          intro hpos; have := h_gap hpos hi hj; rw [ai_eq, bj_eq] at this; exact this
        · exact h_dacc
      have h_vacc' : ∀ k < (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc).size, isValidInterval (if max a[i].1 b[j].1 ≤ min a[i].2 b[j].2 then acc.push (max a[i].1 b[j].1, min a[i].2 b[j].2) else acc)[k]! := by
        split
        · rename_i hlo; exact acc_push_valid _ _ h_vacc hlo
        · exact h_vacc
      split
      · rename_i h_le
        apply helper_pairwiseDisjoint a b (i+1) j _ h_sa h_sb h_da h_db h_va h_vb h_dacc' h_vacc'
        intro hpos hi1 hj'
        have hi1_lt := hi1
        have ai1_eq : a[i+1]! = a[i+1] := by
          simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi1_lt]
        have h_ai_next : a[i].2 < a[i + 1].1 := by
          have := h_da i (i + 1) (by omega) hi1_lt; rw [ai_eq, ai1_eq] at this; exact this
        rw [ai1_eq, bj_eq]
        split
        · rename_i hlo
          rw [push_last_eq]
          show (max a[i].1 b[j].1, min a[i].2 b[j].2).2 < max a[i + 1].1 b[j].1
          simp only
          have hmin : min a[i].2 b[j].2 = a[i].2 := Int.min_eq_left h_le
          rw [hmin]
          exact lt_of_lt_of_le h_ai_next (le_max_left _ _)
        · -- no push case: acc unchanged, need acc.size > 0
          -- hpos says acc.size > 0 (since the if resolved to the else branch, acc' = acc)
          rename_i hno_push
          have hacc_pos : acc.size > 0 := by
            simp [show ¬(max a[i].1 b[j].1 ≤ min a[i].2 b[j].2) from hno_push] at hpos; exact hpos
          have hg := h_gap hacc_pos hi hj; rw [ai_eq, bj_eq] at hg
          have hsort : a[i].1 ≤ a[i + 1].1 := by
            have := h_sa i (i + 1) (by omega) hi1_lt; rw [ai_eq, ai1_eq] at this; exact this
          exact lt_of_lt_of_le hg (max_le_max_right _ hsort)
      · rename_i h_nle
        apply helper_pairwiseDisjoint a b i (j+1) _ h_sa h_sb h_da h_db h_va h_vb h_dacc' h_vacc'
        intro hpos hi' hj1
        have hj1_lt := hj1
        have bj1_eq : b[j+1]! = b[j+1] := by
          simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj1_lt]
        have h_bj_next : b[j].2 < b[j + 1].1 := by
          have := h_db j (j + 1) (by omega) hj1_lt; rw [bj_eq, bj1_eq] at this; exact this
        rw [ai_eq, bj1_eq]
        split
        · rename_i hlo
          rw [push_last_eq]
          show (max a[i].1 b[j].1, min a[i].2 b[j].2).2 < max a[i].1 b[j + 1].1
          simp only
          have hmin : min a[i].2 b[j].2 = b[j].2 := Int.min_eq_right (by omega : b[j].2 ≤ a[i].2)
          rw [hmin]
          exact lt_of_lt_of_le h_bj_next (le_max_right _ _)
        · rename_i hno_push
          have hacc_pos : acc.size > 0 := by
            simp [show ¬(max a[i].1 b[j].1 ≤ min a[i].2 b[j].2) from hno_push] at hpos; exact hpos
          have hg := h_gap hacc_pos hi hj; rw [ai_eq, bj_eq] at hg
          have hsort : b[j].1 ≤ b[j + 1].1 := by
            have := h_sb j (j + 1) (by omega) hj1_lt; rw [bj_eq, bj1_eq] at this; exact this
          exact lt_of_lt_of_le hg (max_le_max_left _ hsort)
    · exact h_dacc
  · exact h_dacc
termination_by a.size - i + b.size - j



theorem correctness_goal_2_0 : ∀ (a b : Array Interval) (i j : ℕ) (acc : Array Interval),
  sortedByStart a →
    sortedByStart b →
      pairwiseDisjointClosed a →
        pairwiseDisjointClosed b →
          (∀ k < a.size, isValidInterval a[k]!) →
            (∀ k < b.size, isValidInterval b[k]!) →
              pairwiseDisjointClosed acc →
                (∀ k < acc.size, isValidInterval acc[k]!) →
                  (acc.size > 0 → i < a.size → j < b.size → acc[acc.size - 1]!.2 < max a[i]!.1 b[j]!.1) →
                    pairwiseDisjointClosed (helper a b i j acc) := by
  intro a b i j acc h_sa h_sb h_da h_db h_va h_vb h_dacc h_vacc h_gap
  exact helper_pairwiseDisjoint a b i j acc h_sa h_sb h_da h_db h_va h_vb h_dacc h_vacc h_gap

theorem correctness_goal_2
    (firstList : Array Interval)
    (secondList : Array Interval)
    (h_precond : precondition firstList secondList)
    : pairwiseDisjointClosed (implementation firstList secondList) := by
    have h_main : ∀ (a b : Array Interval) (i j : ℕ) (acc : Array Interval),
      sortedByStart a →
      sortedByStart b →
      pairwiseDisjointClosed a →
      pairwiseDisjointClosed b →
      (∀ k < a.size, isValidInterval a[k]!) →
      (∀ k < b.size, isValidInterval b[k]!) →
      pairwiseDisjointClosed acc →
      (∀ k < acc.size, isValidInterval acc[k]!) →
      (acc.size > 0 → i < a.size → j < b.size → acc[acc.size - 1]!.2 < max a[i]!.1 b[j]!.1) →
      pairwiseDisjointClosed (helper a b i j acc) := by expose_names; exact (correctness_goal_2_0)
    unfold implementation
    apply h_main
    · exact h_precond.2.2.1
    · exact h_precond.2.2.2.1
    · exact h_precond.2.2.2.2.1
    · exact h_precond.2.2.2.2.2
    · exact h_precond.1
    · exact h_precond.2.1
    · intro i j hij hjsz; simp [Array.size] at hjsz
    · intro k hk; simp [Array.size] at hk
    · intro h; simp [Array.size] at h

theorem correctness_goal_3
        (firstList : Array Interval)
        (secondList : Array Interval)
        (h_precond : precondition firstList secondList)
        (h1 : ∀ k < (implementation firstList secondList).size, isValidInterval (implementation firstList secondList)[k]!)
        (h2 : sortedByStart (implementation firstList secondList))
        (h3 : pairwiseDisjointClosed (implementation firstList secondList))
        : unionIntervalSets (implementation firstList secondList) = unionIntervalSets firstList ∩ unionIntervalSets secondList := by
        sorry

theorem correctness_goal
    (firstList : Array Interval)
    (secondList : Array Interval)
    (h_precond : precondition firstList secondList)
    : postcondition firstList secondList (implementation firstList secondList) := by
    unfold postcondition
    have h1 : ∀ (k : Nat), k < (implementation firstList secondList).size → isValidInterval (implementation firstList secondList)[k]! := by expose_names; exact (correctness_goal_0 firstList secondList)
    have h2 : sortedByStart (implementation firstList secondList) := by expose_names; exact (correctness_goal_1 firstList secondList h_precond)
    have h3 : pairwiseDisjointClosed (implementation firstList secondList) := by expose_names; exact (correctness_goal_2 firstList secondList h_precond)
    have h4 : unionIntervalSets (implementation firstList secondList) = (unionIntervalSets firstList ∩ unionIntervalSets secondList) := by expose_names; exact (correctness_goal_3 firstList secondList h_precond h1 h2 h3)
    exact ⟨h1, h2, h3, h4⟩
end Proof
