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
    1207. Unique Number of Occurrences: decide whether all element-frequency counts in an integer array are pairwise distinct.
    **Important: complexity should be O(n + R²) time and O(R) space**, where R = 2001 is the range of values.
    Natural language breakdown:
    1. Input is an array of integers.
    2. For each integer value v that appears in the array, define occ(v) as the number of indices i with arr[i] = v.
    3. The output is true exactly when for any two distinct values x and y that both appear in the array, occ(x) ≠ occ(y).
    4. Values that do not appear in the array are irrelevant to the uniqueness condition.
    5. The given constraints restrict each element to the range [-1000, 1000].
-/

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
def implementation (arr : Array Int) : Bool :=
  let R := 2001
  let offset := 1000
  -- Step 1: Count occurrences using an array of size R
  let counts := arr.foldl (fun (acc : Array Nat) (v : Int) =>
    let idx := (v + offset).toNat
    acc.set! idx (acc[idx]! + 1)
  ) (mkArray R 0)
  -- Step 2: Collect non-zero counts
  let nonZeroCounts := counts.foldl (fun (acc : Array Nat) (c : Nat) =>
    if c > 0 then acc.push c else acc
  ) #[]
  -- Step 3: Check all non-zero counts are pairwise distinct
  -- Use a nested check: for each pair (i, j) with i < j, check counts differ
  let n := nonZeroCounts.size
  let rec check (i j : Nat) : Bool :=
    if i >= n then true
    else if j >= n then check (i + 1) (i + 2)
    else if nonZeroCounts[i]! == nonZeroCounts[j]! then false
    else check i (j + 1)
  termination_by (n - i, n - j)
  check 0 1
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
#assert_same_evaluation #[(implementation test1_arr), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_arr), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_arr), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_arr), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_arr), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_arr), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_arr), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_arr), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_arr), test9_Expected]
end Assertions

section Pbt
method implementationPbt (arr : Array Int)
  return (result : Bool)
  require precondition arr
  ensures postcondition arr result
  do
  return (implementation arr)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

private theorem mkArray_getElem_zero (i : Nat) (hi : i < (mkArray 2001 (0 : ℤ)).size) :
    (mkArray 2001 (0 : ℤ))[i] = 0 := by
  have hrep : i < (Array.replicate 2001 (0 : ℤ)).size := hi
  exact Array.getElem_mkArray hrep

set_option maxHeartbeats 10000000

private theorem mkArray_getElem!_zero (i : Nat) (hi : i < 2001) :
    (mkArray 2001 (0 : ℤ))[i]! = 0 := by
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  have hlt : i < (mkArray 2001 (0 : ℤ)).size := by
    have : (mkArray 2001 (0 : ℤ)).size = 2001 := Array.size_mkArray
    omega
  simp only [dif_pos hlt]
  exact mkArray_getElem_zero i hlt

set_option maxHeartbeats 10000000

private theorem count_take_zero (arr : Array ℤ) (v : ℤ) :
    Array.count v (arr.take 0) = 0 := by
  rw [Array.count_eq_zero]
  intro h
  have hsz : (arr.take 0).size = 0 := by simp
  exact absurd (Array.eq_empty_of_size_eq_zero hsz ▸ h) (Array.not_mem_empty v)


theorem correctness_goal_0_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (v : ℤ)
    (hv : inProblemRange v)
    : (fun k acc => acc.size = 2001 ∧ ∀ (v : ℤ), inProblemRange v → acc[(v + 1000).toNat]! = Array.count v (arr.take k)) 0
  (mkArray 2001 0) := by
    sorry

theorem array_take_succ_eq_push (arr : Array ℤ) (i : Fin arr.size) :
    arr.take (↑i + 1) = (arr.take ↑i).push arr[i] := by
  simp only [Array.take]
  have h := Array.push_extract_getElem (as := arr) (i := 0) (j := ↑i) i.isLt
  simp [Nat.min_eq_left (Nat.zero_le _)] at h
  -- h was closed by simp, so the goal should be closed too
  -- Let me try differently
  symm
  convert Array.push_extract_getElem (as := arr) (i := 0) (j := ↑i) i.isLt using 1
  simp

theorem getElem!_setIfInBounds_eq {xs : Array ℕ} {i : Nat} {a : ℕ} (h : i < xs.size) :
    (xs.setIfInBounds i a)[i]! = a := by
  simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_setIfInBounds_self, h]

theorem getElem!_setIfInBounds_ne {xs : Array ℕ} {i j : Nat} {a : ℕ} (h : i ≠ j) :
    (xs.setIfInBounds i a)[j]! = xs[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD, Array.getElem?_setIfInBounds_ne h]
  simp only [Array.getElem?_eq_getElem, Array.size_setIfInBounds]
  split
  · next hj =>
    simp [Array.getElem_setIfInBounds_ne hj h]
  · rfl

theorem precond_fin_getElem (arr : Array ℤ) (h_precond : precondition arr) (i : Fin arr.size) :
    inProblemRange arr[i] := by
  unfold precondition at h_precond
  have h := h_precond i.val i.isLt
  simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_eq_getElem, i.isLt] at h
  exact h



theorem correctness_goal_0_1
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (v : ℤ)
    (hv : inProblemRange v)
    : ∀ (i : Fin arr.size) (b : Array ℕ),
  (b.size = 2001 ∧ ∀ (v : ℤ), inProblemRange v → b[(v + 1000).toNat]! = Array.count v (arr.take ↑i)) →
    (fun k acc => acc.size = 2001 ∧ ∀ (v : ℤ), inProblemRange v → acc[(v + 1000).toNat]! = Array.count v (arr.take k))
      (↑i + 1)
      ((fun acc w =>
          let idx := (w + 1000).toNat;
          acc.set! idx (acc[idx]! + 1))
        b arr[i]) := by
    intro i b ⟨hbsize, hbcount⟩
    simp only
    have hw_range : inProblemRange arr[i] := precond_fin_getElem arr h_precond i
    have hidx_lt : (arr[i] + 1000).toNat < b.size := by
      unfold inProblemRange at hw_range; rw [hbsize]; omega
    refine ⟨?_, ?_⟩
    · simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbsize]
    · intro v' hv'
      rw [array_take_succ_eq_push arr i, Array.count_push]
      simp only [Array.set!_eq_setIfInBounds]
      -- Normalize: rewrite goal so arr[↑i] becomes arr[i]
      -- arr[↑i] in the goal is `arr.get ⟨↑i, _⟩` or `arr[i.val]'_`
      -- arr[i] in my hypotheses is `arr.get i` = `arr[i.val]'i.isLt`
      -- They should be the same, but let me try `show` with the right form
      -- Actually let me try a different approach: use congrArg
      -- Or better: just use `change` to unify
      -- Attempt: rewrite everything in terms of a local variable for the element
      set w := arr[i] with hw_def
      -- Now `w = arr[i]`. The goal might still have `arr[↑i]` which is potentially different.
      -- Let me try to also set that:
      -- Actually, after `set w := arr[i]`, Lean should replace all occurrences of `arr[i]` with `w`
      -- If arr[↑i] is a different term, it won't be replaced
      -- Let me try: show that arr[↑i] = w
      have harr_nat : arr[i.val]'(i.isLt) = w := by rfl
      -- In the goal, arr[↑i] is arr[i.val]'(some_proof). Let me try simp
      simp only [show (↑i : ℕ) = i.val from rfl] at *
      -- Now hopefully arr[↑i] = arr[i.val] and we can use harr_nat
      -- Let me try to close with automation after establishing key facts
      by_cases heq : w = v'
      · -- w = v', same index
        subst heq
        simp
        rw [show (w + 1000).toNat = (w + 1000).toNat from rfl]
        rw [getElem!_setIfInBounds_eq hidx_lt]
        rw [← hbcount w hw_range]
      · -- w ≠ v', different indices
        have hidx_ne : (w + 1000).toNat ≠ (v' + 1000).toNat := by
          unfold inProblemRange at hw_range hv'
          intro h; apply heq
          have h1 : (0 : ℤ) ≤ w + 1000 := by omega
          have h2 : (0 : ℤ) ≤ v' + 1000 := by omega
          have := Int.toNat_of_nonneg h1
          have := Int.toNat_of_nonneg h2
          omega
        simp [heq]
        rw [getElem!_setIfInBounds_ne hidx_ne]
        exact hbcount v' hv'

theorem correctness_goal_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    : ∀ (v : ℤ),
  inProblemRange v →
    (Array.foldl
          (fun acc w =>
            let idx := (w + 1000).toNat;
            acc.set! idx (acc[idx]! + 1))
          (mkArray 2001 0) arr)[(v + 1000).toNat]! =
      Array.count v arr := by
    intro v hv
    have h_fold := Array.foldl_induction
      (as := arr)
      (f := fun (acc : Array ℕ) (w : ℤ) =>
            let idx := (w + 1000).toNat;
            acc.set! idx (acc[idx]! + 1))
      (init := mkArray 2001 0)
      (motive := fun (k : ℕ) (acc : Array ℕ) =>
        acc.size = 2001 ∧
        ∀ (v : ℤ), inProblemRange v →
          acc[(v + 1000).toNat]! = (arr.take k).count v)
      ?_ ?_
    · -- Use the conclusion
      have hcounts := h_fold.2 v hv
      rw [hcounts, Array.take_size]
    · -- Base case: motive 0 (mkArray 2001 0)
      expose_names; exact (correctness_goal_0_0 arr h_precond v hv)
    · -- Inductive step
      expose_names; exact (correctness_goal_0_1 arr h_precond v hv)

theorem correctness_goal_1
    (arr : Array ℤ)
    : (Array.foldl
      (fun acc w =>
        let idx := (w + 1000).toNat;
        acc.set! idx (acc[idx]! + 1))
      (mkArray 2001 0) arr).size =
  2001 := by
    have := Array.foldl_induction (as := arr) (motive := fun _ acc => acc.size = 2001)
      (init := mkArray 2001 0)
      (f := fun acc w => let idx := (w + 1000).toNat; acc.set! idx (acc[idx]! + 1))
      (h0 := by native_decide)
      (hf := by
        intro i b hb
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hb])
    exact this

theorem foldl_push_if_eq_filter (xs : Array Nat) :
    Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[] xs = xs.filter (fun c => decide (c > 0)) := by
  have h := @Array.map_filter_eq_foldl Nat Nat id (fun c => decide (c > 0)) xs
  simp [Array.map_id_fun, Function.id_def] at h
  rw [show (fun (acc : Array Nat) (c : Nat) => if c > 0 then acc.push c else acc) =
      (fun acc x => bif decide (0 < x) then acc.push x else acc) from by
    funext acc x; simp [Bool.cond_eq_if, gt_iff_lt]]
  rw [show (fun (c : Nat) => decide (c > 0)) = (fun c => decide (0 < c)) from by
    funext c; simp [gt_iff_lt]]
  exact h.symm

theorem check_correct (nzc : Array Nat) (n : Nat) (hn : n = nzc.size) :
    implementation.check nzc n 0 1 = true ↔
    ∀ (i j : Nat), i < j → j < n → nzc[i]! ≠ nzc[j]! := by
  -- We need to prove this by well-founded induction
  -- First, let's generalize to check i j
  suffices gen : ∀ i j, j > i → i ≤ n →
    (implementation.check nzc n i j = true ↔
     ∀ (i' j' : Nat), i ≤ i' → i' < j' → j' < n →
       (i' > i ∨ j' ≥ j) → nzc[i']! ≠ nzc[j']!) by
    constructor
    · intro h i' j' hij' hj'n
      have := (gen 0 1 (by omega) (by omega)).mp h i' j' (by omega) hij' hj'n
      exact this (by omega)
    · intro h
      rw [(gen 0 1 (by omega) (by omega)).mpr]
      intro i' j' _ hij' hj'n _
      exact h i' j' hij' hj'n
  sorry

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 2000 in
theorem check_unfold (nzc : Array Nat) (n : Nat) (i j : Nat) :
    implementation.check nzc n i j =
    if i >= n then true
    else if j >= n then implementation.check nzc n (i + 1) (i + 2)
    else if nzc[i]! == nzc[j]! then false
    else implementation.check nzc n i (j + 1) := by
  rw [implementation.check]


theorem correctness_goal_2_0
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h_counts_correct : ∀ (v : ℤ),
  inProblemRange v →
    (Array.foldl
          (fun acc w =>
            let idx := (w + 1000).toNat;
            acc.set! idx (acc[idx]! + 1))
          (mkArray 2001 0) arr)[(v + 1000).toNat]! =
      Array.count v arr)
    (h_counts_size : (Array.foldl
      (fun acc w =>
        let idx := (w + 1000).toNat;
        acc.set! idx (acc[idx]! + 1))
      (mkArray 2001 0) arr).size =
  2001)
    (h_cc : ∀ (v : ℤ),
  inProblemRange v →
    (Array.foldl
          (fun acc w =>
            let idx := (w + 1000).toNat;
            acc.set! idx (acc[idx]! + 1))
          (mkArray 2001 0) arr)[(v + 1000).toNat]! =
      Array.count v arr)
    (h_cs : (Array.foldl
      (fun acc w =>
        let idx := (w + 1000).toNat;
        acc.set! idx (acc[idx]! + 1))
      (mkArray 2001 0) arr).size =
  2001)
    (h_pre : precondition arr)
    : (let counts :=
      Array.foldl
        (fun acc v =>
          let idx := (v + 1000).toNat;
          acc.set! idx (acc[idx]! + 1))
        (mkArray 2001 0) arr;
    let nonZeroCounts := Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[] counts;
    let n := nonZeroCounts.size;
    (fun check => check 0 1)
      (implementation.check
        (Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[]
          (Array.foldl (fun acc v => acc.set! (v + 1000).toNat (acc[(v + 1000).toNat]! + 1)) (mkArray 2001 0) arr))
        (Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[]
            (Array.foldl (fun acc v => acc.set! (v + 1000).toNat (acc[(v + 1000).toNat]! + 1)) (mkArray 2001 0)
              arr)).size)) =
    true ↔
  countsAreUnique arr := by
    sorry

theorem correctness_goal_2
    (arr : Array ℤ)
    (h_precond : precondition arr)
    (h_counts_correct : ∀ (v : ℤ),
  inProblemRange v →
    (Array.foldl
          (fun acc w =>
            let idx := (w + 1000).toNat;
            acc.set! idx (acc[idx]! + 1))
          (mkArray 2001 0) arr)[(v + 1000).toNat]! =
      Array.count v arr)
    (h_counts_size : (Array.foldl
      (fun acc w =>
        let idx := (w + 1000).toNat;
        acc.set! idx (acc[idx]! + 1))
      (mkArray 2001 0) arr).size =
  2001)
    : (∀ (v : ℤ),
    inProblemRange v →
      (Array.foldl
            (fun acc w =>
              let idx := (w + 1000).toNat;
              acc.set! idx (acc[idx]! + 1))
            (mkArray 2001 0) arr)[(v + 1000).toNat]! =
        Array.count v arr) →
  (Array.foldl
          (fun acc w =>
            let idx := (w + 1000).toNat;
            acc.set! idx (acc[idx]! + 1))
          (mkArray 2001 0) arr).size =
      2001 →
    precondition arr →
      ((let counts :=
            Array.foldl
              (fun acc v =>
                let idx := (v + 1000).toNat;
                acc.set! idx (acc[idx]! + 1))
              (mkArray 2001 0) arr;
          let nonZeroCounts := Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[] counts;
          let n := nonZeroCounts.size;
          (fun check => check 0 1)
            (implementation.check
              (Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[]
                (Array.foldl (fun acc v => acc.set! (v + 1000).toNat (acc[(v + 1000).toNat]! + 1)) (mkArray 2001 0)
                  arr))
              (Array.foldl (fun acc c => if c > 0 then acc.push c else acc) #[]
                  (Array.foldl (fun acc v => acc.set! (v + 1000).toNat (acc[(v + 1000).toNat]! + 1)) (mkArray 2001 0)
                    arr)).size)) =
          true ↔
        countsAreUnique arr) := by
    intro h_cc h_cs h_pre
    expose_names; exact (correctness_goal_2_0 arr h_precond h_counts_correct h_counts_size h_cc h_cs h_pre)


theorem correctness_goal
    (arr : Array Int)
    (h_precond : precondition arr)
    : postcondition arr (implementation arr) := by
    unfold postcondition
    unfold implementation
    simp only []
    -- We need to show: the result of the implementation equals true iff countsAreUnique arr
    -- Let's define the intermediate arrays
    have h_counts_correct : ∀ (v : Int), inProblemRange v →
      (arr.foldl (fun (acc : Array Nat) (w : Int) =>
        let idx := (w + 1000).toNat
        acc.set! idx (acc[idx]! + 1)
      ) (mkArray 2001 0))[(v + 1000).toNat]! = arr.count v := by expose_names; exact (correctness_goal_0 arr h_precond)
    have h_counts_size : (arr.foldl (fun (acc : Array Nat) (w : Int) =>
        let idx := (w + 1000).toNat
        acc.set! idx (acc[idx]! + 1)
      ) (mkArray 2001 0)).size = 2001 := by expose_names; exact (correctness_goal_1 arr)
    have h_main : (∀ (v : Int), inProblemRange v →
      (arr.foldl (fun (acc : Array Nat) (w : Int) =>
        let idx := (w + 1000).toNat
        acc.set! idx (acc[idx]! + 1)
      ) (mkArray 2001 0))[(v + 1000).toNat]! = arr.count v) →
      (arr.foldl (fun (acc : Array Nat) (w : Int) =>
        let idx := (w + 1000).toNat
        acc.set! idx (acc[idx]! + 1)
      ) (mkArray 2001 0)).size = 2001 →
      precondition arr →
      ((let counts := arr.foldl (fun (acc : Array Nat) (v : Int) =>
          let idx := (v + 1000).toNat
          acc.set! idx (acc[idx]! + 1)
        ) (mkArray 2001 0)
        let nonZeroCounts := counts.foldl (fun (acc : Array Nat) (c : Nat) =>
          if c > 0 then acc.push c else acc
        ) #[]
        let n := nonZeroCounts.size
        let rec check (i j : Nat) : Bool :=
          if i >= n then true
          else if j >= n then check (i + 1) (i + 2)
          else if nonZeroCounts[i]! == nonZeroCounts[j]! then false
          else check i (j + 1)
        termination_by (n - i, n - j)
        check 0 1) = true ↔ countsAreUnique arr) := by expose_names; exact (correctness_goal_2 arr h_precond h_counts_correct h_counts_size)
    exact h_main h_counts_correct h_counts_size h_precond
end Proof
