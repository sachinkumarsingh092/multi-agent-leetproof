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
  -- Range of values is [-1000, 1000], map v ↦ (v + 1000) in [0, 2000]
  let mut counts : Array Nat := Array.replicate 2001 0

  -- First pass: count occurrences of each value
  let mut i : Nat := 0
  while i < arr.size
    -- counts array keeps fixed size (initialized by replicate, preserved by set!)
    invariant "inv_countSize" counts.size = 2001
    -- i is always a valid prefix length of arr
    invariant "inv_iBound" i ≤ arr.size
    -- counts encodes exact occurrence counts for the processed prefix arr[0..i)
    invariant "inv_prefixCounts" (∀ (v : Int), inProblemRange v →
        counts[Int.toNat (v + 1000)]! = (Array.extract arr 0 i).count v)
    decreasing arr.size - i
  do
    let v : Int := arr[i]!
    -- Use Nat index; precondition guarantees v in range
    let idx : Nat := Int.toNat (v + 1000)
    let c : Nat := counts[idx]!
    counts := counts.set! idx (c + 1)
    i := i + 1

  -- Second phase: check pairwise distinctness of positive counts
  let mut ok : Bool := true
  let mut x : Nat := 0
  while x < 2001 ∧ ok = true
    -- x stays within the counts array bounds
    invariant "inv_xBound" x ≤ 2001
    invariant "inv_countSize2" counts.size = 2001
    -- If ok is true, then for every processed index a < x, its positive count differs
    -- from every later positive count (so all comparisons for a have been checked).
    invariant "inv_outerChecked" (ok = true →
      ∀ a b : Nat,
        a < x → a < b → b < 2001 →
        counts[a]! > 0 → counts[b]! > 0 → counts[a]! ≠ counts[b]!)
    -- If ok is false, we have found a concrete duplicate among positive counts.
    invariant "inv_outerFoundDup" (ok = false →
      ∃ a b : Nat,
        a < b ∧ b < 2001 ∧
        counts[a]! > 0 ∧ counts[b]! > 0 ∧ counts[a]! = counts[b]!)
    decreasing 2001 - x
  do
    let cx : Nat := counts[x]!
    if cx = 0 then
      x := x + 1
      continue

    let mut y : Nat := x + 1
    while y < 2001 ∧ ok = true
      invariant "inv_countSize3" counts.size = 2001
      -- y progresses through indices strictly greater than x
      invariant "inv_yBounds" (x + 1 ≤ y ∧ y ≤ 2001)
      -- If ok is still true, cx differs from all positive counts already checked in (x, y)
      invariant "inv_innerChecked" (ok = true →
        ∀ b : Nat,
          x < b → b < y → counts[b]! > 0 → cx ≠ counts[b]!)
      -- If ok is false, we have already found a concrete duplicate for cx.
      invariant "inv_innerFoundDup" (ok = false →
        ∃ b : Nat,
          x < b ∧ b < y ∧
          counts[x]! > 0 ∧ counts[b]! > 0 ∧ counts[x]! = counts[b]!)
      decreasing 2001 - y
    do
      let cy : Nat := counts[y]!
      if cy = 0 then
        y := y + 1
        continue
      if cx = cy then
        ok := false
      y := y + 1

    x := x + 1

  return ok
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

theorem goal_0
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (counts : Array ℕ)
    (i : ℕ)
    (invariant_inv_countSize : counts.size = OfNat.ofNat 2001)
    (if_pos : i < arr.size)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → counts[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i))
    : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → (counts.setIfInBounds (arr[i]! + OfNat.ofNat 1000).toNat (counts[(arr[i]! + OfNat.ofNat 1000).toNat]! + OfNat.ofNat 1))[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  intro v hv_lo hv_hi
  classical

  have hiRange : (-1000 : ℤ) ≤ arr[i]! ∧ arr[i]! ≤ (1000 : ℤ) := by
    simpa using require_1 i if_pos

  set idxA : Nat := (arr[i]! + 1000).toNat with hidxA_def
  set idxV : Nat := (v + 1000).toNat with hidxV_def

  have hidx_lt_2001 (x : ℤ) (hx_lo : (-1000 : ℤ) ≤ x) (hx_hi : x ≤ (1000 : ℤ)) :
      (x + 1000).toNat < 2001 := by
    have hx0 : (0 : ℤ) ≤ x + 1000 := by omega
    have hxlt : x + 1000 < (2001 : ℤ) := by omega
    exact (Int.toNat_lt (n := 2001) (z := x + 1000) hx0).2 hxlt

  have hidxA_lt : idxA < counts.size := by
    have : (arr[i]! + 1000).toNat < 2001 := hidx_lt_2001 (arr[i]!) hiRange.1 hiRange.2
    simpa [idxA, invariant_inv_countSize] using this

  have hidxV_lt : idxV < counts.size := by
    have : (v + 1000).toNat < 2001 := hidx_lt_2001 v (by simpa using hv_lo) (by simpa using hv_hi)
    simpa [idxV, invariant_inv_countSize] using this

  have harr_get : arr[i]'(by exact if_pos) = arr[i]! := by
    simp [Array.getElem!_eq_getD, Array.getD, Array.get?_eq_getElem?, if_pos,
      Array.getElem?_eq_getElem if_pos]

  have hprefix_extract : arr.extract 0 (i + 1) = (arr.extract 0 i).push arr[i]! := by
    have hpush : (arr.extract 0 i).push (arr[i]'(by exact if_pos)) = arr.extract 0 (i + 1) := by
      simpa [Nat.min_eq_left (Nat.zero_le i)] using
        (@Array.push_extract_getElem ℤ arr 0 i if_pos)
    simpa [harr_get] using hpush.symm

  have hcountA : counts[idxA]! = Array.count (arr[i]!) (arr.extract 0 i) := by
    simpa [idxA] using invariant_inv_prefixCounts (arr[i]!) hiRange.1 hiRange.2

  have hcountV : counts[idxV]! = Array.count v (arr.extract 0 i) := by
    simpa [idxV] using invariant_inv_prefixCounts v (by simpa using hv_lo) (by simpa using hv_hi)

  by_cases hvEq : v = arr[i]!
  · have hidxEq : idxV = idxA := by
      simp [idxV, idxA, hvEq]

    have hlhs :
        (counts.setIfInBounds idxA (counts[idxA]! + 1))[idxV]! = counts[idxA]! + 1 := by
      simp [Array.getElem!_eq_getD, Array.getD, Array.get?_eq_getElem?, Array.getElem?_setIfInBounds,
        hidxEq, hidxA_lt]

    have hrhs :
        Array.count v (arr.extract 0 (i + 1)) = Array.count v (arr.extract 0 i) + 1 := by
      calc
        Array.count v (arr.extract 0 (i + 1))
            = Array.count v ((arr.extract 0 i).push arr[i]!) := by
                simpa [hprefix_extract]
        _ = Array.count v ((arr.extract 0 i).push v) := by
              simp [hvEq]
        _ = Array.count v (arr.extract 0 i) + 1 := by
              simpa using (Array.count_push_self (a := v) (xs := arr.extract 0 i))

    calc
      (counts.setIfInBounds idxA (counts[idxA]! + 1))[idxV]!
          = counts[idxA]! + 1 := hlhs
      _ = Array.count v (arr.extract 0 i) + 1 := by
            simpa [hcountA, hvEq]
      _ = Array.count v (arr.extract 0 (i + 1)) := by
            simpa [hrhs]

  · have hidxNe : idxA ≠ idxV := by
      intro hEq
      have hv_lo' : (-1000 : ℤ) ≤ v := by simpa using hv_lo
      have hzV0 : (0 : ℤ) ≤ v + 1000 := by
        have := add_le_add_right hv_lo' (1000 : ℤ)
        simpa [add_assoc, add_left_comm, add_comm] using this
      have hzA0 : (0 : ℤ) ≤ arr[i]! + 1000 := by
        have := add_le_add_right hiRange.1 (1000 : ℤ)
        simpa [add_assoc, add_left_comm, add_comm] using this
      have hcast : ((arr[i]! + 1000).toNat : ℤ) = ((v + 1000).toNat : ℤ) := by
        simpa [idxA, idxV] using congrArg (fun n : Nat => (n : ℤ)) hEq
      have hIntEq : arr[i]! + 1000 = v + 1000 := by
        simpa [Int.toNat_of_nonneg hzA0, Int.toNat_of_nonneg hzV0] using hcast
      have : arr[i]! = v := by omega
      exact hvEq this.symm

    have hlhs : (counts.setIfInBounds idxA (counts[idxA]! + 1))[idxV]! = counts[idxV]! := by
      simp [Array.getElem!_eq_getD, Array.getD, Array.get?_eq_getElem?,
        Array.getElem?_setIfInBounds_ne, hidxV_lt, hidxA_lt, hidxNe]

    have hrhs : Array.count v (arr.extract 0 (i + 1)) = Array.count v (arr.extract 0 i) := by
      have hne : arr[i]! ≠ v := by
        simpa [eq_comm] using hvEq
      calc
        Array.count v (arr.extract 0 (i + 1))
            = Array.count v ((arr.extract 0 i).push arr[i]!) := by
                simpa [hprefix_extract]
        _ = Array.count v (arr.extract 0 i) := by
              simpa using (Array.count_push_of_ne (xs := arr.extract 0 i) (a := v) (b := arr[i]!) hne)

    calc
      (counts.setIfInBounds idxA (counts[idxA]! + 1))[idxV]!
          = counts[idxV]! := hlhs
      _ = Array.count v (arr.extract 0 i) := hcountV
      _ = Array.count v (arr.extract 0 (i + 1)) := by
            simpa [hrhs]

theorem goal_1 : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → (Array.replicate (OfNat.ofNat 2001) (OfNat.ofNat 0))[(v + OfNat.ofNat 1000).toNat]! = OfNat.ofNat 0 := by
  intro v hvL hvU
  -- reduce `get!` on a replicated array to an `if` over the bounds check
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  -- both branches of the bounds check return 0
  by_cases h : v + OfNat.ofNat 1000 < OfNat.ofNat 2001 <;> simp [h]

theorem goal_2
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (x : ℕ)
    (invariant_inv_xBound : x ≤ OfNat.ofNat 2001)
    (a : x < OfNat.ofNat 2001)
    (if_pos : i_1[x]! = OfNat.ofNat 0)
    (invariant_inv_countSize : i_1.size = OfNat.ofNat 2001)
    (invariant_inv_iBound : i_2 ≤ arr.size)
    (done_1 : arr.size ≤ i_2)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → i_1[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i_2))
    (invariant_inv_outerChecked : ∀ (a b : ℕ), a < x → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    : ∀ (a b : ℕ), a < x + OfNat.ofNat 1 → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (x : ℕ)
    (invariant_inv_xBound : x ≤ OfNat.ofNat 2001)
    (a : x < OfNat.ofNat 2001)
    (if_neg : ¬i_1[x]! = OfNat.ofNat 0)
    (y : ℕ)
    (invariant_inv_countSize3 : i_1.size = OfNat.ofNat 2001)
    (a_2 : x + OfNat.ofNat 1 ≤ y)
    (a_3 : y ≤ OfNat.ofNat 2001)
    (a_4 : y < OfNat.ofNat 2001)
    (if_pos : i_1[y]! = OfNat.ofNat 0)
    (invariant_inv_countSize : i_1.size = OfNat.ofNat 2001)
    (invariant_inv_iBound : i_2 ≤ arr.size)
    (done_1 : arr.size ≤ i_2)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → i_1[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i_2))
    (invariant_inv_outerChecked : ∀ (a b : ℕ), a < x → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (invariant_inv_innerChecked : ∀ (b : ℕ), x < b → b < y → OfNat.ofNat 0 < i_1[b]! → ¬i_1[x]! = i_1[b]!)
    : ∀ (b : ℕ), x < b → b < y + OfNat.ofNat 1 → OfNat.ofNat 0 < i_1[b]! → ¬i_1[x]! = i_1[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_4
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (x : ℕ)
    (invariant_inv_xBound : x ≤ OfNat.ofNat 2001)
    (a : x < OfNat.ofNat 2001)
    (if_neg : ¬i_1[x]! = OfNat.ofNat 0)
    (y : ℕ)
    (invariant_inv_countSize3 : i_1.size = OfNat.ofNat 2001)
    (a_2 : x + OfNat.ofNat 1 ≤ y)
    (a_3 : y ≤ OfNat.ofNat 2001)
    (a_4 : y < OfNat.ofNat 2001)
    (if_neg_1 : ¬i_1[y]! = OfNat.ofNat 0)
    (if_neg_2 : ¬i_1[x]! = i_1[y]!)
    (invariant_inv_countSize : i_1.size = OfNat.ofNat 2001)
    (invariant_inv_iBound : i_2 ≤ arr.size)
    (done_1 : arr.size ≤ i_2)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → i_1[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i_2))
    (invariant_inv_outerChecked : ∀ (a b : ℕ), a < x → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (invariant_inv_innerChecked : ∀ (b : ℕ), x < b → b < y → OfNat.ofNat 0 < i_1[b]! → ¬i_1[x]! = i_1[b]!)
    : ∀ (b : ℕ), x < b → b < y + OfNat.ofNat 1 → OfNat.ofNat 0 < i_1[b]! → ¬i_1[x]! = i_1[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_5
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (x : ℕ)
    (invariant_inv_xBound : x ≤ OfNat.ofNat 2001)
    (a : x < OfNat.ofNat 2001)
    (if_neg : ¬i_1[x]! = OfNat.ofNat 0)
    (invariant_inv_countSize3 : i_1.size = OfNat.ofNat 2001)
    (i_4 : Bool)
    (y_1 : ℕ)
    (invariant_inv_countSize : i_1.size = OfNat.ofNat 2001)
    (invariant_inv_iBound : i_2 ≤ arr.size)
    (a_2 : x + OfNat.ofNat 1 ≤ y_1)
    (a_3 : y_1 ≤ OfNat.ofNat 2001)
    (done_1 : arr.size ≤ i_2)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → i_1[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i_2))
    (invariant_inv_outerChecked : ∀ (a b : ℕ), a < x → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (invariant_inv_innerChecked : i_4 = true → ∀ (b : ℕ), x < b → b < y_1 → OfNat.ofNat 0 < i_1[b]! → ¬i_1[x]! = i_1[b]!)
    (done_3 : y_1 < OfNat.ofNat 2001 → i_4 = false)
    : i_4 = true → ∀ (a b : ℕ), a < x + OfNat.ofNat 1 → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_6
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (x : ℕ)
    (invariant_inv_xBound : x ≤ OfNat.ofNat 2001)
    (a : x < OfNat.ofNat 2001)
    (if_neg : ¬i_1[x]! = OfNat.ofNat 0)
    (invariant_inv_countSize3 : i_1.size = OfNat.ofNat 2001)
    (i_4 : Bool)
    (y_1 : ℕ)
    (invariant_inv_countSize : i_1.size = OfNat.ofNat 2001)
    (invariant_inv_iBound : i_2 ≤ arr.size)
    (a_2 : x + OfNat.ofNat 1 ≤ y_1)
    (a_3 : y_1 ≤ OfNat.ofNat 2001)
    (done_1 : arr.size ≤ i_2)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → i_1[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i_2))
    (invariant_inv_outerChecked : ∀ (a b : ℕ), a < x → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (invariant_inv_innerFoundDup : i_4 = false → ∃ b, x < b ∧ b < y_1 ∧ OfNat.ofNat 0 < i_1[x]! ∧ OfNat.ofNat 0 < i_1[b]! ∧ i_1[x]! = i_1[b]!)
    : i_4 = false → ∃ a b, a < b ∧ b < OfNat.ofNat 2001 ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[b]! ∧ i_1[a]! = i_1[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_7
    (arr : Array ℤ)
    (require_1 : ∀ i < arr.size, -OfNat.ofNat 1000 ≤ arr[i]! ∧ arr[i]! ≤ OfNat.ofNat 1000)
    (i_1 : Array ℕ)
    (i_2 : ℕ)
    (i_4 : Bool)
    (x_1 : ℕ)
    (invariant_inv_iBound : i_2 ≤ arr.size)
    (invariant_inv_xBound : x_1 ≤ OfNat.ofNat 2001)
    (done_1 : arr.size ≤ i_2)
    (invariant_inv_prefixCounts : ∀ (v : ℤ), -OfNat.ofNat 1000 ≤ v → v ≤ OfNat.ofNat 1000 → i_1[(v + OfNat.ofNat 1000).toNat]! = Array.count v (arr.extract (OfNat.ofNat 0) i_2))
    (invariant_inv_outerFoundDup : i_4 = false → ∃ a b, a < b ∧ b < OfNat.ofNat 2001 ∧ OfNat.ofNat 0 < i_1[a]! ∧ OfNat.ofNat 0 < i_1[b]! ∧ i_1[a]! = i_1[b]!)
    (invariant_inv_outerChecked : i_4 = true → ∀ (a b : ℕ), a < x_1 → a < b → b < OfNat.ofNat 2001 → OfNat.ofNat 0 < i_1[a]! → OfNat.ofNat 0 < i_1[b]! → ¬i_1[a]! = i_1[b]!)
    (done_2 : x_1 < OfNat.ofNat 2001 → i_4 = false)
    : postcondition arr i_4 := by
  unfold postcondition countsAreUnique

  -- First pass finished: i_2 = arr.size
  have hi2 : i_2 = arr.size := Nat.le_antisymm invariant_inv_iBound done_1

  -- counts array encodes true counts for whole array
  have hcount : ∀ (v : ℤ), (-1000 : ℤ) ≤ v → v ≤ (1000 : ℤ) →
      i_1[(v + 1000).toNat]! = Array.count v arr := by
    intro v hvL hvU
    simpa [hi2, Array.extract_size] using (invariant_inv_prefixCounts v hvL hvU)

  -- Any element of arr is in range, using require_1
  have range_of_mem : ∀ {v : ℤ}, v ∈ arr → (-1000 : ℤ) ≤ v ∧ v ≤ (1000 : ℤ) := by
    intro v hv
    rcases Array.getElem_of_mem hv with ⟨i, hi, rfl⟩
    have h := require_1 i hi
    have hget : arr[i]! = arr[i]'hi := by
      simp [Array.getElem!_eq_getD, Array.getD, hi]
    simpa [hget] using h

  -- index bound for any in-range integer
  have idx_lt_2001 : ∀ {v : ℤ}, (-1000 : ℤ) ≤ v → v ≤ (1000 : ℤ) → (v + 1000).toNat < 2001 := by
    intro v hvL hvU
    have hnonneg : (0 : ℤ) ≤ v + 1000 := by linarith
    have hlt : v + 1000 < (2001 : ℤ) := by linarith
    exact (Int.toNat_lt (n := 2001) (z := v + 1000) hnonneg).2 hlt

  constructor
  · intro hi4
    -- show countsAreUnique arr
    intro x y hxy hxmem hymem

    have hxRange := range_of_mem (v := x) hxmem
    have hyRange := range_of_mem (v := y) hymem

    -- positivity of counts
    have hxCountPos : 0 < Array.count x arr := (Array.count_pos_iff (a := x) (xs := arr)).2 hxmem
    have hyCountPos : 0 < Array.count y arr := (Array.count_pos_iff (a := y) (xs := arr)).2 hymem

    have hix_lt : (x + 1000).toNat < 2001 := idx_lt_2001 (v := x) hxRange.1 hxRange.2
    have hiy_lt : (y + 1000).toNat < 2001 := idx_lt_2001 (v := y) hyRange.1 hyRange.2

    -- indices are different
    have hidx_ne : (x + 1000).toNat ≠ (y + 1000).toNat := by
      intro hEq
      have hx0 : (0 : ℤ) ≤ x + 1000 := by linarith [hxRange.1]
      have hy0 : (0 : ℤ) ≤ y + 1000 := by linarith [hyRange.1]
      have hEqI : ((x + 1000).toNat : ℤ) = ((y + 1000).toNat : ℤ) :=
        congrArg (fun n : Nat => (n : ℤ)) hEq
      have hsum : x + 1000 = y + 1000 := by
        calc
          x + 1000 = ((x + 1000).toNat : ℤ) := by
            simpa using (Int.toNat_of_nonneg hx0).symm
          _ = ((y + 1000).toNat : ℤ) := hEqI
          _ = y + 1000 := by
            simpa using (Int.toNat_of_nonneg hy0)
      have : x = y := by linarith
      exact hxy this

    -- From done_2: if i_4=true then x_1 = 2001
    have hx1_ge : 2001 ≤ x_1 := by
      have : ¬ x_1 < 2001 := by
        intro hxlt
        have hi4false : i_4 = false := done_2 hxlt
        cases hi4false ▸ hi4
      exact Nat.le_of_not_gt this
    have hx1_eq : x_1 = 2001 := Nat.le_antisymm invariant_inv_xBound hx1_ge

    -- rewrite positivity into i_1 entries
    have hxI1Pos : 0 < i_1[(x + 1000).toNat]! := by
      simpa [hcount x hxRange.1 hxRange.2] using hxCountPos
    have hyI1Pos : 0 < i_1[(y + 1000).toNat]! := by
      simpa [hcount y hyRange.1 hyRange.2] using hyCountPos

    -- apply outerChecked on the corresponding indices (ordered)
    have hneqI1 : ¬ i_1[(x + 1000).toNat]! = i_1[(y + 1000).toNat]! := by
      rcases lt_or_gt_of_ne hidx_ne with hlt | hgt
      · have ha_x1 : (x + 1000).toNat < x_1 := by simpa [hx1_eq] using hix_lt
        exact invariant_inv_outerChecked hi4 _ _ ha_x1 hlt hiy_lt hxI1Pos hyI1Pos
      · have ha_x1 : (y + 1000).toNat < x_1 := by simpa [hx1_eq] using hiy_lt
        have hneq := invariant_inv_outerChecked hi4 _ _ ha_x1 hgt hix_lt hyI1Pos hxI1Pos
        simpa [eq_comm] using hneq

    -- translate back to counts
    simpa [hcount x hxRange.1 hxRange.2, hcount y hyRange.1 hyRange.2] using hneqI1

  · intro hUnique
    -- show i_4 = true (contrapositive using the found-duplicate invariant)
    by_contra hi4ne
    have hi4false : i_4 = false := by
      cases h : i_4 with
      | false => rfl
      | true => cases hi4ne h

    rcases invariant_inv_outerFoundDup hi4false with ⟨a, b, hab, hbLt, haPos, hbPos, habEq⟩

    let vA : ℤ := (a : ℤ) - 1000
    let vB : ℤ := (b : ℤ) - 1000

    have haLt2001 : a < 2001 := lt_trans hab hbLt
    have haLe2000 : a ≤ 2000 := Nat.le_of_lt_succ haLt2001
    have hbLe2000 : b ≤ 2000 := Nat.le_of_lt_succ hbLt

    have hvA_L : (-1000 : ℤ) ≤ vA := by
      have : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast (Nat.zero_le a)
      dsimp [vA]
      linarith
    have hvA_U : vA ≤ (1000 : ℤ) := by
      have ha' : (a : ℤ) ≤ (2000 : ℤ) := by exact_mod_cast haLe2000
      dsimp [vA]
      linarith
    have hvB_L : (-1000 : ℤ) ≤ vB := by
      have : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.zero_le b)
      dsimp [vB]
      linarith
    have hvB_U : vB ≤ (1000 : ℤ) := by
      have hb' : (b : ℤ) ≤ (2000 : ℤ) := by exact_mod_cast hbLe2000
      dsimp [vB]
      linarith

    have idxA : (vA + 1000).toNat = a := by
      dsimp [vA]
      simp
    have idxB : (vB + 1000).toNat = b := by
      dsimp [vB]
      simp

    have hA_count : i_1[a]! = Array.count vA arr := by
      simpa [idxA] using hcount vA hvA_L hvA_U
    have hB_count : i_1[b]! = Array.count vB arr := by
      simpa [idxB] using hcount vB hvB_L hvB_U

    have hcountA_pos : 0 < Array.count vA arr := by
      simpa [hA_count] using haPos
    have hcountB_pos : 0 < Array.count vB arr := by
      simpa [hB_count] using hbPos

    have hmemA : vA ∈ arr := (Array.count_pos_iff (a := vA) (xs := arr)).1 hcountA_pos
    have hmemB : vB ∈ arr := (Array.count_pos_iff (a := vB) (xs := arr)).1 hcountB_pos

    have hvA_ne_hvB : vA ≠ vB := by
      dsimp [vA, vB]
      have habI : (a : ℤ) < (b : ℤ) := by exact_mod_cast hab
      linarith

    have hcountsEq : Array.count vA arr = Array.count vB arr := by
      have : i_1[a]! = i_1[b]! := habEq
      simpa [hA_count, hB_count] using this

    have := hUnique vA vB hvA_ne_hvB hmemA hmemB
    exact this hcountsEq


prove_correct UniqueNumberOfOccurrences by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 arr require_1 counts i invariant_inv_countSize if_pos invariant_inv_prefixCounts)
  exact (goal_1)
  exact (goal_2 arr require_1 i_1 i_2 x invariant_inv_xBound a if_pos invariant_inv_countSize invariant_inv_iBound done_1 invariant_inv_prefixCounts invariant_inv_outerChecked)
  exact (goal_3 arr require_1 i_1 i_2 x invariant_inv_xBound a if_neg y invariant_inv_countSize3 a_2 a_3 a_4 if_pos invariant_inv_countSize invariant_inv_iBound done_1 invariant_inv_prefixCounts invariant_inv_outerChecked invariant_inv_innerChecked)
  exact (goal_4 arr require_1 i_1 i_2 x invariant_inv_xBound a if_neg y invariant_inv_countSize3 a_2 a_3 a_4 if_neg_1 if_neg_2 invariant_inv_countSize invariant_inv_iBound done_1 invariant_inv_prefixCounts invariant_inv_outerChecked invariant_inv_innerChecked)
  exact (goal_5 arr require_1 i_1 i_2 x invariant_inv_xBound a if_neg invariant_inv_countSize3 i_4 y_1 invariant_inv_countSize invariant_inv_iBound a_2 a_3 done_1 invariant_inv_prefixCounts invariant_inv_outerChecked invariant_inv_innerChecked done_3)
  exact (goal_6 arr require_1 i_1 i_2 x invariant_inv_xBound a if_neg invariant_inv_countSize3 i_4 y_1 invariant_inv_countSize invariant_inv_iBound a_2 a_3 done_1 invariant_inv_prefixCounts invariant_inv_outerChecked invariant_inv_innerFoundDup)
  exact (goal_7 arr require_1 i_1 i_2 i_4 x_1 invariant_inv_iBound invariant_inv_xBound done_1 invariant_inv_prefixCounts invariant_inv_outerFoundDup invariant_inv_outerChecked done_2)
end Proof
