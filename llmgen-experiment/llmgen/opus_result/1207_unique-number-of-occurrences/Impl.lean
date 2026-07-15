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
    1207. Unique Number of Occurrences: decide whether all element-frequency counts in an integer array are pairwise distinct.
    **Important: complexity should be O(n + R²) time and O(R) space**, where R = 2001 is the range of values.
    Natural language breakdown:
    1. Input is an array of integers.
    2. For each integer value v that appears in the array, define occ(v) as the number of indices i with arr[i] = v.
    3. The output is true exactly when for any two distinct values x and y that both appear in the array, occ(x) ≠ occ(y).
    4. Values that do not appear in the array are irrelevant to the uniqueness condition.
    5. The given constraints restrict each element to the range [-1000, 1000].
-/

section Specs
-- Helper predicate for the stated input-range constraint.
def inProblemRange (x : Int) : Prop :=
  (-1000 ≤ x) ∧ (x ≤ 1000)

-- The core semantic property: occurrence counts are unique among values that appear.
def countsAreUnique (arr : Array Int) : Prop :=
  ∀ (x : Int) (y : Int), x ≠ y → x ∈ arr → y ∈ arr → arr.count x ≠ arr.count y

-- Preconditions
-- We adopt the problem's stated range constraint as an explicit precondition.
def precondition (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → inProblemRange (arr[i]!)

-- Postconditions
-- result is true iff the array has unique occurrence counts among all values that appear.
def postcondition (arr : Array Int) (result : Bool) : Prop :=
  (result = true ↔ countsAreUnique arr)
end Specs

section Impl
method UniqueNumberOfOccurrences (arr : Array Int)
  return (result : Bool)
  require precondition arr
  ensures postcondition arr result
  do
  -- Count occurrences using an array of size 2001 (for values -1000 to 1000)
  let R := 2001
  let mut counts : Array Nat := Array.replicate R 0
  -- Phase 1: count occurrences O(n)
  let mut i := 0
  while i < arr.size
    -- Bounds on loop counter
    -- Init: i=0, so 0 ≤ 0 ∧ 0 ≤ arr.size. Pres: i increments up to arr.size. Suff: terminates when i=arr.size.
    invariant "i_bounds" 0 ≤ i ∧ i ≤ arr.size
    -- Size of counts array is preserved through set! operations
    -- Init: Array.replicate R 0 has size R. Pres: set! preserves size. Suff: needed for Phase 2 indexing.
    invariant "counts_size_1" counts.size = R
    -- Partial counting: counts[idx] = occurrences of (idx-1000) in arr[0..i)
    -- Init: all counts are 0 and take 0 is []. Pres: incrementing counts[idx] matches adding arr[i] to counted prefix.
    -- Suff: at loop exit i=arr.size, take arr.size = full list, giving complete counts.
    invariant "partial_count" ∀ (idx : Nat), idx < R →
      counts[idx]! = (arr.toList.take i).count (↑idx - 1000 : Int)
    decreasing arr.size - i
  do
    let v := arr[i]!
    let idx := (v + 1000).toNat
    counts := counts.set! idx (counts[idx]! + 1)
    i := i + 1
  -- Phase 2: check uniqueness of non-zero counts O(R^2)
  let mut unique := true
  let mut j := 0
  while j < R
    -- Bounds on outer loop counter
    invariant "j_bounds" 0 ≤ j ∧ j ≤ R
    -- Counts array size preserved (no mutations in phase 2)
    invariant "counts_size_2" counts.size = R
    -- Counts reflect full array (established at end of Phase 1, preserved since counts is not mutated)
    invariant "full_count" ∀ (idx : Nat), idx < R →
      counts[idx]! = arr.toList.count (↑idx - 1000 : Int)
    -- If unique became false, there exist two distinct indices with matching non-zero counts
    -- Init: unique=true so vacuously true. Pres: only set false when duplicate found. Suff: provides witness for ¬countsAreUnique.
    invariant "unique_false_witness" unique = false →
      ∃ (a b : Nat), a < R ∧ b < R ∧ a ≠ b ∧ counts[a]! > 0 ∧ counts[b]! > 0 ∧ counts[a]! = counts[b]!
    -- If unique is still true, all pairs with first index < j have been verified distinct
    -- Init: j=0, vacuously true. Pres: inner loop checks all partners of j. Suff: at j=R, all pairs checked.
    invariant "unique_true_checked" unique = true →
      ∀ (a b : Nat), a < j → b < R → a ≠ b → counts[a]! > 0 → counts[b]! > 0 → counts[a]! ≠ counts[b]!
    decreasing R - j
  do
    if counts[j]! > 0 then
      let mut k := j + 1
      while k < R
        -- Bounds on inner loop counter
        invariant "k_bounds" j + 1 ≤ k ∧ k ≤ R
        -- Counts array size preserved
        invariant "counts_size_3" counts.size = R
        -- Counts still reflect full array
        invariant "full_count_inner" ∀ (idx : Nat), idx < R →
          counts[idx]! = arr.toList.count (↑idx - 1000 : Int)
        -- If unique is false, duplicate witness exists
        invariant "unique_false_inner" unique = false →
          ∃ (a b : Nat), a < R ∧ b < R ∧ a ≠ b ∧ counts[a]! > 0 ∧ counts[b]! > 0 ∧ counts[a]! = counts[b]!
        -- If unique is true: all previous rows checked, and current row checked up to k
        -- Init: k=j+1, inner conjunction vacuous. Pres: each k step extends checked range.
        -- Suff: at k=R, combined with symmetry of ≠, gives full coverage for row j.
        invariant "unique_true_inner" unique = true →
          (∀ (a b : Nat), a < j → b < R → a ≠ b → counts[a]! > 0 → counts[b]! > 0 → counts[a]! ≠ counts[b]!) ∧
          (∀ (b : Nat), j < b → b < k → counts[b]! > 0 → counts[j]! ≠ counts[b]!)
        decreasing R - k
      do
        if counts[k]! > 0 then
          if counts[j]! = counts[k]! then
            unique := false
        k := k + 1
    j := j + 1
  return unique
end Impl

section TestCases
-- Test case 1: Example 1
-- arr = [1,2,2,1,1,3] has counts: 1↦3, 2↦2, 3↦1 (all distinct)
def test1_arr : Array Int := #[1, 2, 2, 1, 1, 3]
def test1_Expected : Bool := true

-- Test case 2: Example 2
-- arr = [1,2] has counts 1↦1, 2↦1 (not unique)
def test2_arr : Array Int := #[1, 2]
def test2_Expected : Bool := false

-- Test case 3: Example 3
-- arr = [-3,0,1,-3,1,1,1,-3,10,0] has counts -3↦3, 0↦2, 1↦4, 10↦1 (all distinct)
def test3_arr : Array Int := #[-3, 0, 1, -3, 1, 1, 1, -3, 10, 0]
def test3_Expected : Bool := true

-- Test case 4: Empty array (vacuously unique)
def test4_arr : Array Int := #[]
def test4_Expected : Bool := true

-- Test case 5: Singleton array (vacuously unique)
def test5_arr : Array Int := #[0]
def test5_Expected : Bool := true

-- Test case 6: All same value (only one distinct value, so unique)
def test6_arr : Array Int := #[7, 7, 7, 7]
def test6_Expected : Bool := true

-- Test case 7: Two distinct values with the same count
-- counts: 1↦2, 2↦2
def test7_arr : Array Int := #[1, 1, 2, 2]
def test7_Expected : Bool := false

-- Test case 8: Three values where two share the same count
-- counts: 1↦2, 2↦1, 3↦2
def test8_arr : Array Int := #[1, 3, 1, 2, 3]
def test8_Expected : Bool := false

-- Test case 9: Boundary values within allowed range
-- counts: -1000↦1, 1000↦2, 0↦3 (all distinct)
def test9_arr : Array Int := #[-1000, 1000, 1000, 0, 0, 0]
def test9_Expected : Bool := true

-- Recommend to validate: test1_arr, test3_arr, test9_arr
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((UniqueNumberOfOccurrences test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((UniqueNumberOfOccurrences test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((UniqueNumberOfOccurrences test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((UniqueNumberOfOccurrences test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((UniqueNumberOfOccurrences test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((UniqueNumberOfOccurrences test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((UniqueNumberOfOccurrences test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((UniqueNumberOfOccurrences test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((UniqueNumberOfOccurrences test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test UniqueNumberOfOccurrences (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem Array.getElem!_setIfInBounds {α : Type*} [Inhabited α] {xs : Array α} {i j : Nat} {a : α}
    (hj : j < xs.size) :
    (xs.setIfInBounds i a)[j]! = if i = j then a else xs[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_setIfInBounds]
  split
  · -- i = j
    subst_vars
    simp [hj]
  · -- i ≠ j
    rfl

theorem Array.toList_getElem_eq_getElem! {α : Type*} [Inhabited α] {xs : Array α} {i : Nat}
    (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]! := by
  have hi : i < xs.size := by simp [Array.length_toList] at h; exact h
  rw [Array.getElem_toList (by exact hi)]
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by exact hi)]


theorem goal_0
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (counts : Array ℕ)
    (i : ℕ)
    (invariant_counts_size_1 : counts.size = OfNat.ofNat 2001)
    (invariant_partial_count : ∀ idx < OfNat.ofNat 2001, counts[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take i arr.toList))
    (if_pos : i < arr.size)
    : ∀ idx < OfNat.ofNat 2001, (counts.setIfInBounds (arr[i]! + OfNat.ofNat 1000).toNat (counts[(arr[i]! + OfNat.ofNat 1000).toNat]! + OfNat.ofNat 1))[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take (i + OfNat.ofNat 1) arr.toList) := by
    have hrange : -1000 ≤ arr[i]! ∧ arr[i]! ≤ 1000 := require_1 i if_pos
    have hv_nonneg : 0 ≤ arr[i]! + 1000 := by omega
    have htoNat_cast : ((arr[i]! + 1000).toNat : ℤ) = arr[i]! + 1000 := Int.toNat_of_nonneg hv_nonneg
    have hv_lt : (arr[i]! + 1000).toNat < 2001 := by
      have h1 : arr[i]! + 1000 < 2001 := by omega
      rw [show (2001 : ℕ) = (2001 : ℤ).toNat from rfl]
      exact (Int.toNat_lt hv_nonneg).mpr h1
    have hi_lt_len : i < arr.toList.length := by simp [Array.length_toList]; omega
    have htake_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr.toList[i]'hi_lt_len] :=
      List.take_succ_eq_append_getElem hi_lt_len
    have harr_toList_get : (arr.toList[i]'hi_lt_len : ℤ) = arr[i]! :=
      Array.toList_getElem_eq_getElem! hi_lt_len
    intro idx hidx
    rw [htake_succ, List.count_append, List.count_singleton, harr_toList_get]
    have hidx_lt : idx < counts.size := by omega
    rw [Array.getElem!_setIfInBounds hidx_lt]
    by_cases heq : (arr[i]! + 1000).toNat = idx
    · -- Case: idx is the updated index
      simp [heq]
      have hcast : arr[i]! = (↑idx : ℤ) - 1000 := by
        have : (↑idx : ℤ) = arr[i]! + 1000 := by rw [← heq]; exact htoNat_cast
        omega
      simp [hcast]
      rw [← heq, invariant_partial_count _ hv_lt]
    · -- Case: idx is not the updated index
      simp [heq]
      have hne_val : arr[i]! ≠ ↑idx - 1000 := by
        intro h
        apply heq
        have : arr[i]! + 1000 = ↑idx := by omega
        rw [← Int.toNat_natCast idx]
        congr 1
      simp [hne_val]
      exact invariant_partial_count idx hidx

theorem goal_1
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (counts : Array ℕ)
    (i : ℕ)
    (a_1 : i ≤ arr.size)
    (invariant_counts_size_1 : counts.size = OfNat.ofNat 2001)
    (invariant_partial_count : ∀ idx < OfNat.ofNat 2001, counts[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take i arr.toList))
    (if_pos : i < arr.size)
    : arr.size - (i + OfNat.ofNat 1) < arr.size - i := by
    intros; expose_names; try simp_all; try grind

theorem goal_2 : ∀ idx < OfNat.ofNat 2001, (Array.replicate (OfNat.ofNat 2001) (OfNat.ofNat 0))[idx]! = OfNat.ofNat 0 := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (i_1 : Array ℕ)
    (j : ℕ)
    (if_pos : j < OfNat.ofNat 2001)
    (k : ℕ)
    (a_4 : j + OfNat.ofNat 1 ≤ k)
    (if_pos_2 : k < OfNat.ofNat 2001)
    (if_pos_4 : i_1[j]! = i_1[k]!)
    (if_pos_1 : OfNat.ofNat 0 < i_1[j]!)
    (if_pos_3 : OfNat.ofNat 0 < i_1[k]!)
    : ∃ a < OfNat.ofNat 2001, ∃ x < OfNat.ofNat 2001, ¬a = x ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[x]! ∧ i_1[a]! = i_1[x]! := by
    have a_4' : j + 1 ≤ k := a_4
    have hjk : j ≠ k := by omega
    exact ⟨j, if_pos, k, if_pos_2, hjk, if_pos_1, if_pos_3, if_pos_4⟩

theorem goal_4
    (k : ℕ)
    (if_pos_2 : k < OfNat.ofNat 2001)
    : OfNat.ofNat 2000 - k < OfNat.ofNat 2001 - k := by
    show 2000 - k < 2001 - k
    have hk : k < 2001 := if_pos_2
    omega

theorem goal_5
    (i_1 : Array ℕ)
    (j : ℕ)
    (k : ℕ)
    (unique_1 : Bool)
    (a_4 : j + OfNat.ofNat 1 ≤ k)
    (a_5 : k ≤ OfNat.ofNat 2001)
    (if_pos_2 : k < OfNat.ofNat 2001)
    (if_neg : ¬i_1[j]! = i_1[k]!)
    (invariant_unique_true_inner : unique_1 = true → (∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!) ∧ ∀ (b : ℕ), j < b → b < k → OfNat.ofNat 0 < i_1[b]! → ¬i_1[j]! = i_1[b]!)
    (if_pos_3 : OfNat.ofNat 0 < i_1[k]!)
    : unique_1 = true → (∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!) ∧ ∀ (b : ℕ), j < b → b < k + OfNat.ofNat 1 → OfNat.ofNat 0 < i_1[b]! → ¬i_1[j]! = i_1[b]! := by
    intro h_true
    obtain ⟨h_checked, h_inner⟩ := invariant_unique_true_inner h_true
    constructor
    · exact h_checked
    · intro b hj hbk hpos
      have hbk_nat : b < k + 1 := hbk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hbk_nat with hlt | heq
      · exact h_inner b hj hlt hpos
      · subst heq
        exact if_neg

theorem goal_6
    (k : ℕ)
    (if_pos_2 : k < OfNat.ofNat 2001)
    : OfNat.ofNat 2000 - k < OfNat.ofNat 2001 - k := by
    intros; expose_names; exact goal_4 k if_pos_2

theorem goal_7
    (i_1 : Array ℕ)
    (j : ℕ)
    (k : ℕ)
    (unique_1 : Bool)
    (a_4 : j + OfNat.ofNat 1 ≤ k)
    (a_5 : k ≤ OfNat.ofNat 2001)
    (if_pos_2 : k < OfNat.ofNat 2001)
    (invariant_unique_true_inner : unique_1 = true → (∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!) ∧ ∀ (b : ℕ), j < b → b < k → OfNat.ofNat 0 < i_1[b]! → ¬i_1[j]! = i_1[b]!)
    (if_neg : i_1[k]! = OfNat.ofNat 0)
    : unique_1 = true → (∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!) ∧ ∀ (b : ℕ), j < b → b < k + OfNat.ofNat 1 → OfNat.ofNat 0 < i_1[b]! → ¬i_1[j]! = i_1[b]! := by
    intro h
    obtain ⟨h1, h2⟩ := invariant_unique_true_inner h
    refine ⟨h1, ?_⟩
    intro b hjb hbk1 hpos
    have hbk_or : b < k ∨ b = k := by
      have : b < k + 1 := by
        have := hbk1
        simp only [OfNat.ofNat] at this
        exact this
      omega
    rcases hbk_or with hbk | hbek
    · exact h2 b hjb hbk hpos
    · subst hbek
      have : i_1[b]! = 0 := by
        have := if_neg
        simp only [OfNat.ofNat] at this ⊢
        exact this
      simp only [OfNat.ofNat] at hpos
      omega

theorem goal_8
    (k : ℕ)
    (if_pos_2 : k < OfNat.ofNat 2001)
    : OfNat.ofNat 2000 - k < OfNat.ofNat 2001 - k := by
    intros; expose_names; exact goal_6 k if_pos_2

theorem goal_9
    (i_1 : Array ℕ)
    (unique_2 : Bool)
    (invariant_unique_false_inner : unique_2 = false → ∃ a < OfNat.ofNat 2001, ∃ x < OfNat.ofNat 2001, ¬a = x ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[x]! ∧ i_1[a]! = i_1[x]!)
    : unique_2 = false → ∃ a < OfNat.ofNat 2001, ∃ x < OfNat.ofNat 2001, ¬a = x ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[x]! ∧ i_1[a]! = i_1[x]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_10
    (i_1 : Array ℕ)
    (j : ℕ)
    (unique : Bool)
    (a_3 : j ≤ OfNat.ofNat 2001)
    (if_pos : j < OfNat.ofNat 2001)
    (i_4 : ℕ)
    (unique_2 : Bool)
    (a_4 : j + OfNat.ofNat 1 ≤ i_4)
    (invariant_unique_true_checked : unique = true → ∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (if_pos_1 : OfNat.ofNat 0 < i_1[j]!)
    (a : True)
    (done_3 : OfNat.ofNat 2001 ≤ i_4)
    (invariant_unique_true_inner : unique_2 = true → (∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!) ∧ ∀ (b : ℕ), j < b → b < i_4 → OfNat.ofNat 0 < i_1[b]! → ¬i_1[j]! = i_1[b]!)
    : unique_2 = true → ∀ (a b : ℕ), a < j + OfNat.ofNat 1 → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]! := by
    intro hu2 a b ha hb hab hpa hpb
    obtain ⟨H1, H2⟩ := invariant_unique_true_inner hu2
    have halej : a ≤ j := Nat.lt_add_one_iff.mp ha
    rcases Nat.eq_or_lt_of_le halej with haeqj | haltj
    · -- a = j
      subst haeqj
      by_cases hblt : b < a
      · intro heq
        have hab' : ¬ b = a := Nat.ne_of_lt hblt
        exact H1 b a hblt if_pos hab' hpb hpa heq.symm
      · have haltb : a < b := by
          cases Nat.lt_or_ge b a with
          | inl h => exact absurd h hblt
          | inr h =>
            exact h.lt_of_ne (fun heq => hab heq)
        have hbi4 : b < i_4 := Nat.lt_of_lt_of_le hb done_3
        exact H2 b haltb hbi4 hpb
    · exact H1 a b haltj hb hab hpa hpb

theorem goal_11
    (j : ℕ)
    (if_pos : j < OfNat.ofNat 2001)
    : OfNat.ofNat 2000 - j < OfNat.ofNat 2001 - j := by
    intros; expose_names; exact goal_6 j if_pos

theorem goal_12
    (i_1 : Array ℕ)
    (j : ℕ)
    (unique : Bool)
    (a_3 : j ≤ OfNat.ofNat 2001)
    (if_pos : j < OfNat.ofNat 2001)
    (invariant_unique_true_checked : unique = true → ∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (if_neg : i_1[j]! = OfNat.ofNat 0)
    (a : True)
    : unique = true → ∀ (a b : ℕ), a < j + OfNat.ofNat 1 → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]! := by
    intro hu a b ha hb hab hpa hpb
    have : OfNat.ofNat 1 = (1 : ℕ) := rfl
    have : OfNat.ofNat 0 = (0 : ℕ) := rfl
    have : OfNat.ofNat 2001 = (2001 : ℕ) := rfl
    by_cases haj : a < j
    · exact invariant_unique_true_checked hu a b haj hb hab hpa hpb
    · have haj2 : a = j := by omega
      subst haj2
      rw [if_neg] at hpa
      simp at hpa

theorem goal_13
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (j : ℕ)
    (unique : Bool)
    (a_3 : j ≤ OfNat.ofNat 2001)
    (if_pos : j < OfNat.ofNat 2001)
    (invariant_counts_size_1 : i_1.size = OfNat.ofNat 2001)
    (a_1 : i_2 ≤ arr.size)
    (invariant_partial_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take i_2 arr.toList))
    (invariant_full_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = Array.count (idx.cast - OfNat.ofNat 1000) arr)
    (invariant_unique_false_witness : unique = false → ∃ a < OfNat.ofNat 2001, ∃ x < OfNat.ofNat 2001, ¬a = x ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[x]! ∧ i_1[a]! = i_1[x]!)
    (invariant_unique_true_checked : unique = true → ∀ (a b : ℕ), a < j → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (if_neg : i_1[j]! = OfNat.ofNat 0)
    (done_1 : arr.size ≤ i_2)
    : OfNat.ofNat 2000 - j < OfNat.ofNat 2001 - j := by
    intros; expose_names; try simp_all; try grind

theorem goal_14
    (arr : Array ℤ)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (a_1 : i_2 ≤ arr.size)
    (invariant_partial_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take i_2 arr.toList))
    (done_1 : arr.size ≤ i_2)
    : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = Array.count (idx.cast - OfNat.ofNat 1000) arr := by
    have h_eq : i_2 = arr.size := Nat.le_antisymm a_1 done_1
    intro idx h_idx
    rw [invariant_partial_count idx h_idx, h_eq, ← Array.count_toList]
    congr 1
    exact List.take_of_length_le (by rw [Array.length_toList])

theorem goal_15
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (invariant_counts_size_2 : i_1.size = OfNat.ofNat 2001)
    (i_4 : ℕ)
    (unique_1 : Bool)
    (invariant_counts_size_1 : i_1.size = OfNat.ofNat 2001)
    (a_1 : i_2 ≤ arr.size)
    (invariant_partial_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take i_2 arr.toList))
    (a_3 : i_4 ≤ OfNat.ofNat 2001)
    (invariant_full_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = Array.count (idx.cast - OfNat.ofNat 1000) arr)
    (a : True)
    (done_1 : arr.size ≤ i_2)
    (a_2 : True)
    (done_2 : OfNat.ofNat 2001 ≤ i_4)
    (invariant_unique_false_witness : unique_1 = false → ∃ a < OfNat.ofNat 2001, ∃ x < OfNat.ofNat 2001, ¬a = x ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[x]! ∧ i_1[a]! = i_1[x]!)
    (invariant_unique_true_checked : unique_1 = true → ∀ (a b : ℕ), a < i_4 → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    : postcondition arr unique_1 := by
    sorry



theorem goal_15
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (invariant_counts_size_2 : i_1.size = OfNat.ofNat 2001)
    (i_4 : ℕ)
    (unique_1 : Bool)
    (invariant_counts_size_1 : i_1.size = OfNat.ofNat 2001)
    (a_1 : i_2 ≤ arr.size)
    (invariant_partial_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = List.count (idx.cast - OfNat.ofNat 1000) (List.take i_2 arr.toList))
    (a_3 : i_4 ≤ OfNat.ofNat 2001)
    (invariant_full_count : ∀ idx < OfNat.ofNat 2001, i_1[idx]! = Array.count (idx.cast - OfNat.ofNat 1000) arr)
    (a : True)
    (done_1 : arr.size ≤ i_2)
    (a_2 : True)
    (done_2 : OfNat.ofNat 2001 ≤ i_4)
    (invariant_unique_false_witness : unique_1 = false → ∃ a < OfNat.ofNat 2001, ∃ x < OfNat.ofNat 2001, ¬a = x ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[x]! ∧ i_1[a]! = i_1[x]!)
    (invariant_unique_true_checked : unique_1 = true → ∀ (a b : ℕ), a < i_4 → b < OfNat.ofNat 2001 → ¬a = b → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    : postcondition arr unique_1 := by
    sorry



prove_correct UniqueNumberOfOccurrences by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 arr require_1 counts i invariant_counts_size_1 invariant_partial_count if_pos)
  exact (goal_1 arr require_1 counts i a_1 invariant_counts_size_1 invariant_partial_count if_pos)
  exact (goal_2)
  exact (goal_3 i_1 j if_pos k a_4 if_pos_2 if_pos_4 if_pos_1 if_pos_3)
  exact (goal_4 k if_pos_2)
  exact (goal_5 i_1 j k unique_1 a_4 a_5 if_pos_2 if_neg invariant_unique_true_inner if_pos_3)
  exact (goal_6 k if_pos_2)
  exact (goal_7 i_1 j k unique_1 a_4 a_5 if_pos_2 invariant_unique_true_inner if_neg)
  exact (goal_8 k if_pos_2)
  exact (goal_9 i_1 unique_2 invariant_unique_false_inner)
  exact (goal_10 i_1 j unique a_3 if_pos i_4 unique_2 a_4 invariant_unique_true_checked if_pos_1 a done_3 invariant_unique_true_inner)
  exact (goal_11 j if_pos)
  exact (goal_12 i_1 j unique a_3 if_pos invariant_unique_true_checked if_neg a)
  exact (goal_13 arr require_1 i_1 i_2 j unique a_3 if_pos invariant_counts_size_1 a_1 invariant_partial_count invariant_full_count invariant_unique_false_witness invariant_unique_true_checked if_neg done_1)
  exact (goal_14 arr i_1 i_2 a_1 invariant_partial_count done_1)
  exact (goal_15 arr require_1 i_1 i_2 invariant_counts_size_2 i_4 unique_1 invariant_counts_size_1 a_1 invariant_partial_count a_3 invariant_full_count a done_1 a_2 done_2 invariant_unique_false_witness invariant_unique_true_checked)
end Proof
