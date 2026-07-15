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
    1089. Duplicate Zeros: duplicate each occurrence of 0 in a fixed-length integer array, shifting right and truncating.
    Natural language breakdown:
    1. Input is an array of integers with a fixed length n.
    2. We define a conceptual output stream obtained by scanning the input left-to-right.
    3. Each nonzero input element contributes exactly one output element equal to itself.
    4. Each zero input element contributes exactly two consecutive output elements, both equal to 0.
    5. The actual returned array is the first n elements of this conceptual output stream (truncate to length n).
    6. Because the original problem updates in-place and returns nothing, we model the modified array as a returned array.
    7. Therefore the result must have the same size as the input.
    8. Every output index j (0 ≤ j < n) is produced by a unique input index i, determined by how many output elements are produced by prefixes of the input.
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: producedLen arr k = number of conceptual output elements produced by the first k input elements.
-- Each nonzero produces 1; each zero produces 2.
-- We use foldl over a prefix (arr.take k) to avoid recursion.
-- Note: we use Int = 0 propositionally; this is fine (not Float).
def producedLen (arr : Array Int) (k : Nat) : Nat :=
  (arr.take k).foldl (fun (acc : Nat) (x : Int) => if x = 0 then acc + 2 else acc + 1) 0

-- Precondition: none.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition: result is the length-preserving truncation of duplicating zeros.
-- We characterize the mapping index-wise using the prefix produced lengths.
-- For each output index j, there is a unique input index i < n such that
-- producedLen arr i ≤ j < producedLen arr (i+1). The output value equals arr[i], but if arr[i]=0 then it is 0.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∀ (j : Nat), j < arr.size →
    ∃! (i : Nat),
      i < arr.size ∧
      producedLen arr i ≤ j ∧
      j < producedLen arr (i + 1) ∧
      result[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))
end Specs

section Impl
method DuplicateZeros (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  let n := arr.size
  -- First pass: compute the conceptual length after duplicating zeros
  let mut total : Nat := 0
  let mut i : Nat := 0
  while i < n
    -- i stays within the scanned prefix bounds.
    -- Init: i=0; Preserved by i:=i+1; Exit gives i=n.
    invariant "dz_pass1_i_le_n" i ≤ n
    -- total equals the conceptual produced length of the first i elements.
    -- Init: producedLen arr 0 = 0; Each step adds 1 or 2 matching producedLen's fold.
    invariant "dz_pass1_total" total = producedLen arr i
    -- Remember the definition of n.
    invariant "dz_pass1_n" n = arr.size
    decreasing n - i
  do
    if arr[i]! = 0 then
      total := total + 2
    else
      total := total + 1
    i := i + 1

  -- Second pass (from right to left): write into a fresh array of size n,
  -- simulating in-place right shift with truncation.
  let mut res : Array Int := Array.replicate n (0 : Int)
  let mut writePos : Nat := total
  let mut idx : Nat := n
  while idx > 0
    -- idx ranges over [0,n].
    invariant "dz_pass2_idx_le_n" idx ≤ n
    -- res always has fixed size n.
    invariant "dz_pass2_res_size" res.size = n
    -- writePos tracks the conceptual produced length of the prefix arr.take idx.
    -- Init: idx=n and writePos=total=producedLen arr n; Each processed element decrements by 1 or 2.
    invariant "dz_pass2_writePos" writePos = producedLen arr idx
    -- All already-written output positions j in [writePos, n) satisfy the final postcondition characterization.
    -- Init: when writePos ≥ n the range is empty; Preservation: body only writes at positions < previous writePos.
    invariant "dz_pass2_suffix_correct"
      (∀ (j : Nat), j < n → writePos ≤ j →
        ∃! (i : Nat),
          i < n ∧
          producedLen arr i ≤ j ∧
          j < producedLen arr (i + 1) ∧
          res[j]! = (if arr[i]! = 0 then (0 : Int) else arr[i]!))
    decreasing idx
  do
    idx := idx - 1
    let x := arr[idx]!
    if x = 0 then
      -- Write two zeros conceptually at positions writePos-2 and writePos-1
      if writePos > 0 then
        writePos := writePos - 1
        if writePos < n then
          res := res.set! writePos (0 : Int)
      if writePos > 0 then
        writePos := writePos - 1
        if writePos < n then
          res := res.set! writePos (0 : Int)
    else
      -- Write one element at position writePos-1
      if writePos > 0 then
        writePos := writePos - 1
        if writePos < n then
          res := res.set! writePos x

  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,0,2,3,0,4,5,0]
-- Output: [1,0,0,2,3,0,0,4]
def test1_arr : Array Int := #[1, 0, 2, 3, 0, 4, 5, 0]
def test1_Expected : Array Int := #[1, 0, 0, 2, 3, 0, 0, 4]

-- Test case 2: Example 2 (no zeros)
def test2_arr : Array Int := #[1, 2, 3]
def test2_Expected : Array Int := #[1, 2, 3]

-- Test case 3: empty array
def test3_arr : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: single element zero
def test4_arr : Array Int := #[0]
def test4_Expected : Array Int := #[0]

-- Test case 5: single element nonzero
def test5_arr : Array Int := #[7]
def test5_Expected : Array Int := #[7]

-- Test case 6: all zeros (truncation preserves all zeros)
def test6_arr : Array Int := #[0, 0, 0]
def test6_Expected : Array Int := #[0, 0, 0]

-- Test case 7: zeros causing truncation of later elements
-- [1,0,0,2] -> conceptual: 1,0,0,0,0,2 -> take 4 => [1,0,0,0]
def test7_arr : Array Int := #[1, 0, 0, 2]
def test7_Expected : Array Int := #[1, 0, 0, 0]

-- Test case 8: negative values with zeros
-- [0,-1,0,2] -> conceptual: 0,0,-1,0,0,2 -> take 4 => [0,0,-1,0]
def test8_arr : Array Int := #[0, -1, 0, 2]
def test8_Expected : Array Int := #[0, 0, -1, 0]

-- Test case 9: trailing zero does not create a visible extra element after truncation
-- [1,2,0] -> conceptual: 1,2,0,0 -> take 3 => [1,2,0]
def test9_arr : Array Int := #[1, 2, 0]
def test9_Expected : Array Int := #[1, 2, 0]

-- Recommend to validate: boundary sizes (0/1), multiple zeros, truncation at end
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((DuplicateZeros test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((DuplicateZeros test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((DuplicateZeros test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((DuplicateZeros test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((DuplicateZeros test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((DuplicateZeros test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((DuplicateZeros test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((DuplicateZeros test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((DuplicateZeros test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test DuplicateZeros (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (arr : Array ℤ)
    (i : ℕ)
    (invariant_dz_pass1_i_le_n : i ≤ arr.size)
    (if_pos : i < arr.size)
    (if_pos_1 : arr[i]! = OfNat.ofNat 0)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) + OfNat.ofNat 2 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) := by
  classical

  have hi1_le : i + 1 ≤ arr.size := Nat.succ_le_of_lt if_pos
  have hmin1 : min i arr.size = i := Nat.min_eq_left invariant_dz_pass1_i_le_n
  have hmin2 : min (i + 1) arr.size = i + 1 := Nat.min_eq_left hi1_le

  have hget : arr[i]! = arr[i] := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, if_pos]
  have hi0 : arr[i] = (0 : ℤ) := by
    simpa [hget] using if_pos_1

  let f : Nat → ℤ → Nat := fun acc x => if x = (0 : ℤ) then acc + 2 else acc + 1

  -- reduce to simplified goal
  suffices
      Array.foldl f 0 (arr.extract 0 i) 0 i + 2 = Array.foldl f 0 (arr.extract 0 (i + 1)) 0 (i + 1) by
    simpa [hmin1, hmin2, f]

  have hpush : (arr.extract 0 i).push arr[i] = arr.extract 0 (i + 1) := by
    simpa using (@Array.push_extract_getElem ℤ arr 0 i if_pos)

  have hxSize : (arr.extract 0 i).size = i := by
    simpa using (@Array.size_extract_of_le ℤ arr 0 i invariant_dz_pass1_i_le_n)

  have hrhs : Array.foldl f 0 (arr.extract 0 (i + 1)) 0 (i + 1) = Array.foldl f 0 (arr.extract 0 i) 0 i + 2 := by
    let fM : Nat → ℤ → Id Nat := fun acc x => pure (f acc x)
    have w : (i + 1) = (arr.extract 0 i).size + 1 := by
      simpa [hxSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

    calc
      Array.foldl f 0 (arr.extract 0 (i + 1)) 0 (i + 1)
          = Array.foldl f 0 ((arr.extract 0 i).push arr[i]) 0 (i + 1) := by
              simpa [hpush]
      _ = (Array.foldlM (m := Id) fM 0 ((arr.extract 0 i).push arr[i]) 0 (i + 1)).run := by
              simpa [fM] using
                (Array.foldl_eq_foldlM (xs := (arr.extract 0 i).push arr[i]) (f := f)
                  (b := 0) (start := 0) (stop := i + 1))
      _ = ((Array.foldlM (m := Id) fM 0 (arr.extract 0 i) 0 i) >>= fun b => fM b arr[i]).run := by
              have h := (Array.foldlM_push' (xs := (arr.extract 0 i)) (a := arr[i]) (f := fM)
                (b := 0) (stop := i + 1) (m := Id) (w := w))
              simpa [fM, w, hxSize] using congrArg (fun t => t.run) h
      _ = (f ((Array.foldlM (m := Id) fM 0 (arr.extract 0 i) 0 i).run) arr[i]) := by
              -- reduce `Id` bind/run
              rfl
      _ = (f (Array.foldl f 0 (arr.extract 0 i) 0 i) arr[i]) := by
              -- rewrite the inner foldlM.run to foldl
              have hinner : Array.foldl f 0 (arr.extract 0 i) 0 i = (Array.foldlM (m := Id) fM 0 (arr.extract 0 i) 0 i).run := by
                simpa [fM] using
                  (Array.foldl_eq_foldlM (xs := arr.extract 0 i) (f := f) (b := 0)
                    (start := 0) (stop := i))
              -- use the symmetric form
              simpa using congrArg (fun t => f t arr[i]) hinner.symm
      _ = Array.foldl f 0 (arr.extract 0 i) 0 i + 2 := by
              simp [f, hi0]

  -- finish
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrhs.symm

theorem goal_1
    (arr : Array ℤ)
    (i : ℕ)
    (invariant_dz_pass1_i_le_n : i ≤ arr.size)
    (if_pos : i < arr.size)
    (if_neg : ¬arr[i]! = OfNat.ofNat 0)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) + OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) := by
  classical
  have hi1 : i + 1 ≤ arr.size := Nat.succ_le_of_lt if_pos
  -- simplify the `min` bounds
  simp [Nat.min_eq_left invariant_dz_pass1_i_le_n, Nat.min_eq_left hi1]

  -- prefix array
  set xs : Array ℤ := arr.extract 0 i
  have hsize : xs.size = i := by
    subst xs
    simpa using (@Array.size_extract_of_le _ arr 0 i invariant_dz_pass1_i_le_n)

  -- connect get! with bounded getElem
  have hget : arr[i]! = (arr[i]'if_pos) := by
    simp [Array.get!, if_pos]

  -- extract 0 (i+1) is xs with the next element pushed
  have hpush0 : xs.push (arr[i]'if_pos) = arr.extract 0 (i + 1) := by
    subst xs
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem _ arr 0 i if_pos)
  have hpush : xs.push arr[i]! = arr.extract 0 (i + 1) := by
    simpa [hget] using hpush0

  rw [← hpush]

  -- switch to foldlM/Id so we can use `foldlM_push'`
  rw [Array.foldl_eq_foldlM]
  rw [Array.foldl_eq_foldlM]

  let f : Nat → ℤ → Id Nat := fun acc x =>
    pure (if x = (0 : ℤ) then acc + 2 else acc + 1)

  have hw : (i + 1) = xs.size + 1 := by simpa [hsize]
  have hfoldM :
      Array.foldlM f 0 (xs.push arr[i]!) 0 (i + 1) =
        xs.foldlM f 0 >>= fun b => f b (arr[i]!) := by
    simpa [hw] using
      (Array.foldlM_push' (m := Id) (xs := xs) (a := arr[i]!) (f := f) (b := 0) (stop := i + 1) (w := hw))

  have hxs : xs.foldlM f 0 = xs.foldlM f 0 0 i := by
    simp [Array.foldlM, hsize]

  have hfoldM_run := congrArg Id.run hfoldM

  -- finish by simplifying Id and the final if-branch (nonzero → +1)
  simpa [f, hxs, if_neg] using hfoldM_run.symm

theorem goal_2
    (arr : Array ℤ)
    (idx : ℕ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    -- apply the +2 step lemma for a zero at position idx-1
    have hlt_idx : idx - 1 < idx := by
      -- pred idx < idx, then rewrite pred idx = idx - 1
      simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt if_pos))

    have hlt : idx - 1 < arr.size :=
      lt_of_lt_of_le hlt_idx invariant_dz_pass2_idx_le_n

    have hle : idx - 1 ≤ arr.size :=
      le_trans (Nat.sub_le idx 1) invariant_dz_pass2_idx_le_n

    have hidx : (idx - 1) + 1 = idx := by
      simpa using (Nat.sub_one_add_one_eq_of_pos if_pos)

    have hstep0 :
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0)
          (min (idx - OfNat.ofNat 1) arr.size) + OfNat.ofNat 2
          =
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) ((idx - OfNat.ofNat 1) + OfNat.ofNat 1)) (OfNat.ofNat 0)
          (min ((idx - OfNat.ofNat 1) + OfNat.ofNat 1) arr.size) := by
      simpa using (goal_0 arr (idx - 1) hle hlt if_pos_1)

    have hstep :
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0)
          (min (idx - OfNat.ofNat 1) arr.size) + OfNat.ofNat 2
          =
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0)
          (min idx arr.size) := by
      simpa [hidx] using hstep0

    -- now subtract 2 from both sides
    have :
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - 2
          =
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0)
          (min (idx - OfNat.ofNat 1) arr.size) := by
      -- rewrite the RHS using hstep, then cancel
      -- hstep : P(idx-1) + 2 = P(idx)
      -- so P(idx) - 2 = (P(idx-1) + 2) - 2 = P(idx-1)
      calc
        Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
            (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - 2
            =
          (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
              (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0)
              (min (idx - OfNat.ofNat 1) arr.size) + 2) - 2 := by
            simpa [hstep] using (rfl :
              (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
                  (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - 2)
                =
              (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
                  (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - 2))
        _ =
          Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
            (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0)
            (min (idx - OfNat.ofNat 1) arr.size) := by
          simpa [Nat.add_sub_cancel]

    -- finish by rewriting -1 -1 as -2
    simpa [Nat.sub_sub, this]

theorem goal_3
    (arr : Array ℤ)
    (i_1 : ℕ)
    (idx : ℕ)
    (res : Array ℤ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (invariant_dz_pass2_res_size : res.size = arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size)
    (if_pos : OfNat.ofNat 0 < idx)
    (done_1 : arr.size ≤ i_1)
    (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!)
    (if_pos_2 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size))
    (if_pos_3 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 < arr.size)
    (if_pos_4 : OfNat.ofNat 1 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size))
    (if_pos_5 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1 < arr.size)
    : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j + OfNat.ofNat 1 + OfNat.ofNat 1 → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ ((res.setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) (OfNat.ofNat 0)).setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1) (OfNat.ofNat 0))[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
  intro j hj hWle
  classical

  let F : Nat → Nat := fun k =>
    Array.foldl (fun acc x => if x = (0:ℤ) then acc + 2 else acc + 1) 0 (arr.extract 0 k) 0 (min k arr.size)

  have hWpos : 0 < F idx := by simpa [F] using if_pos_2
  have hWgt1 : 1 < F idx := by simpa [F] using if_pos_4

  have getBang_setIfInBounds_ne (xs : Array ℤ) (i j : Nat) (a : ℤ)
      (hij : i ≠ j) : (xs.setIfInBounds i a)[j]! = xs[j]! := by
    by_cases hj' : j < xs.size
    · simpa [Array.getElem!_eq_getD, Array.getD, hj',
        Array.getElem_setIfInBounds_ne (xs := xs) (i := i) (a := a) (j := j) hj' hij]
    · have hjle : xs.size ≤ j := Nat.le_of_not_gt hj'
      simp [Array.getElem!_eq_getD, Array.getD, hj', Array.getElem?_size_le (xs := xs) (i := j) hjle]

  have getBang_setIfInBounds_self (xs : Array ℤ) (i : Nat) (a : ℤ)
      (hi : i < xs.size) : (xs.setIfInBounds i a)[i]! = a := by
    simpa [Array.getElem!_eq_getD, Array.getD, hi, Array.getElem_setIfInBounds (xs := xs) (i := i) (a := a) (j := i) hi]

  have F_lt_succ (t : Nat) (ht : t < arr.size) : F t < F (t + 1) := by
    by_cases h0 : arr[t]! = (0:ℤ)
    · have hEq := goal_0 arr t (Nat.le_of_lt ht) ht (by simpa using h0)
      have hEq' : F t + 2 = F (t+1) := by simpa [F] using hEq
      have : F t < F t + 2 := by omega
      simpa [hEq'] using this
    · have hEq := goal_1 arr t (Nat.le_of_lt ht) ht (by simpa using h0)
      have hEq' : F t + 1 = F (t+1) := by simpa [F] using hEq
      have : F t < F t + 1 := Nat.lt_succ_self (F t)
      simpa [hEq'] using this

  have F_mono {a b : Nat} (hab : a ≤ b) (hb : b ≤ arr.size) : F a ≤ F b := by
    have hP : ∀ d, a + d ≤ arr.size → F a ≤ F (a + d) := by
      intro d hd
      induction d with
      | zero =>
          simpa using (le_rfl : F a ≤ F a)
      | succ d ih =>
          have hd' : a + d ≤ arr.size := by omega
          have htlt : a + d < arr.size := by omega
          have hstep : F (a + d) ≤ F (a + d + 1) := le_of_lt (F_lt_succ (a + d) htlt)
          have : F a ≤ F (a + d) := ih hd'
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using le_trans this hstep
    have hdle : a + (b - a) ≤ arr.size := by
      simpa [Nat.add_sub_of_le hab] using hb
    have : F a ≤ F (a + (b - a)) := hP (b - a) hdle
    simpa [Nat.add_sub_of_le hab] using this

  have hF_idx_pred : F idx - 1 - 1 = F (idx - 1) := by
    have h := goal_2 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos
    simpa [F] using h
  have hF_pred_eq : F (idx - 1) = F idx - 1 - 1 := Eq.symm hF_idx_pred

  let res' : Array ℤ := (res.setIfInBounds (F idx - 1) 0).setIfInBounds (F idx - 1 - 1) 0

  by_cases hjge : F idx ≤ j
  · have hexu := invariant_dz_pass2_suffix_correct j hj (by simpa [F] using hjge)
    have hne1 : F idx - 1 ≠ j := by omega
    have hne2 : F idx - 1 - 1 ≠ j := by omega
    have hresj : res'[j]! = res[j]! := by
      dsimp [res']
      have h1 : ((res.setIfInBounds (F idx - 1) 0).setIfInBounds (F idx - 1 - 1) 0)[j]! =
          (res.setIfInBounds (F idx - 1) 0)[j]! := by
        simpa using
          (getBang_setIfInBounds_ne (xs := res.setIfInBounds (F idx - 1) 0) (i := F idx - 1 - 1) (j := j) (a := (0:ℤ)) hne2)
      have h2 : (res.setIfInBounds (F idx - 1) 0)[j]! = res[j]! := by
        simpa using (getBang_setIfInBounds_ne (xs := res) (i := F idx - 1) (j := j) (a := (0:ℤ)) hne1)
      exact h1.trans h2

    rcases hexu with ⟨i, hi, huniq⟩
    refine ⟨i, ?_, ?_⟩
    · rcases hi with ⟨hiLt, hFiLe, hjLt, hval⟩
      refine ⟨hiLt, hFiLe, hjLt, ?_⟩
      exact hresj.trans hval
    · intro i' hi'
      apply huniq
      rcases hi' with ⟨hi'Lt, hFiLe, hjLt, hval⟩
      refine ⟨hi'Lt, hFiLe, hjLt, ?_⟩
      exact hresj.symm.trans hval

  · have hjlt : j < F idx := lt_of_not_ge hjge
    have hWle' : F idx ≤ j + 2 := by
      simpa [F, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hWle
    have hj1le : j + 1 ≤ F idx := Nat.succ_le_of_lt hjlt
    have hj_cases : j = F idx - 1 ∨ j = F idx - 1 - 1 := by
      have hcase : F idx ≤ j + 1 ∨ j + 1 < F idx := le_or_lt (F idx) (j + 1)
      cases hcase with
      | inl hWle1 =>
          have hWeq : F idx = j + 1 := Nat.le_antisymm hWle1 hj1le
          left
          simpa [hWeq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      | inr hj1lt =>
          have hj2le : j + 2 ≤ F idx := Nat.succ_le_of_lt hj1lt
          have hWeq : F idx = j + 2 := Nat.le_antisymm hWle' hj2le
          right
          simpa [hWeq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

    have hidx1_lt : idx - 1 < arr.size := by omega

    have hFpred_le : F (idx - 1) ≤ j := by
      rcases hj_cases with rfl | rfl
      · have : F idx - 1 - 1 ≤ F idx - 1 := by omega
        simpa [hF_pred_eq] using this
      · simpa [hF_pred_eq]

    have hres'_val : res'[j]! = 0 := by
      rcases hj_cases with rfl | rfl
      · have hjRes : (F idx - 1) < res.size := by
          simpa [F, invariant_dz_pass2_res_size] using if_pos_3
        have hne : (F idx - 1 - 1) ≠ (F idx - 1) := by omega
        simp [res', getBang_setIfInBounds_ne, getBang_setIfInBounds_self, hjRes, hne]
      · have hjRes : (F idx - 1 - 1) < res.size := by
          simpa [F, invariant_dz_pass2_res_size] using if_pos_5
        simp [res', getBang_setIfInBounds_self, hjRes]

    refine ⟨idx - 1, ?_, ?_⟩
    · refine ⟨hidx1_lt, hFpred_le, ?_, ?_⟩
      · have hidxSubAdd : idx - 1 + 1 = idx :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt (by simpa using if_pos))
        simpa [F, hidxSubAdd] using hjlt
      · have : (if arr[idx - 1]! = (0:ℤ) then (0:ℤ) else arr[idx - 1]!) = 0 := by
          simp [if_pos_1]
        simpa [this] using hres'_val

    · intro i' hi'
      rcases hi' with ⟨hi'Lt, hFiLe, hjLt, -⟩
      have hi'_lt_idx : i' < idx := by
        by_contra hcontra
        have hle : idx ≤ i' := Nat.le_of_not_gt hcontra
        have hi'_le_size : i' ≤ arr.size := Nat.le_of_lt hi'Lt
        have hmono' : F idx ≤ F i' := F_mono hle hi'_le_size
        have : F idx ≤ j := le_trans hmono' hFiLe
        exact (not_le_of_lt hjlt) this

      have hidx1_le_i' : idx - 1 ≤ i' := by
        by_contra hcontra
        have hi'1_le : i' + 1 ≤ idx - 1 := by omega
        have hidx1_le_size : idx - 1 ≤ arr.size := by omega
        have hmono' : F (i' + 1) ≤ F (idx - 1) := F_mono hi'1_le hidx1_le_size
        have hFi1_le_j : F (i' + 1) ≤ j := le_trans hmono' hFpred_le
        exact (not_lt_of_ge hFi1_le_j) hjLt

      omega

theorem goal_4
    (arr : Array ℤ)
    (idx : ℕ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    (if_pos_2 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size))
    (if_neg : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ OfNat.ofNat 1)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
  set t : Nat :=
    Array.foldl (fun acc x => if x = (0 : ℤ) then acc + 2 else acc + 1) 0
      (arr.extract 0 idx) 0 (min idx arr.size)
  set p : Nat :=
    Array.foldl (fun acc x => if x = (0 : ℤ) then acc + 2 else acc + 1) 0
      (arr.extract 0 (idx - 1)) 0 (min (idx - 1) arr.size)

  have ht_pos : 0 < t := by
    simpa [t] using if_pos_2
  have ht_ge1 : (1 : Nat) ≤ t := by
    -- 1 ≤ t ↔ 0 < t
    simpa using (Nat.succ_le_iff.2 ht_pos)
  have ht_le1 : t ≤ 1 := by
    simpa [t] using if_neg
  have ht1 : t = 1 := by
    exact Nat.le_antisymm ht_le1 ht_ge1

  have h2 : t - 1 - 1 = p := by
    simpa [t, p] using (goal_2 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos)

  have hp0 : p = 0 := by
    have hsub : t - 1 - 1 = 0 := by
      simp [ht1]
    exact Eq.trans h2.symm hsub

  have : t - 1 = p := by
    simp [ht1, hp0]

  simpa [t, p] using this

theorem goal_5
    (arr : Array ℤ)
    (i_1 : ℕ)
    (idx : ℕ)
    (res : Array ℤ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size)
    (if_pos : OfNat.ofNat 0 < idx)
    (if_neg : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ OfNat.ofNat 1)
    : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j + OfNat.ofNat 1 → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (res.setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) (OfNat.ofNat 0))[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
  -- This branch is unreachable: the last element is zero, so the produced length
  -- of the prefix cannot be ≤ 1.
  have hFalse : False := by
    let f : Nat → ℤ → Nat := fun acc x => if x = (0 : ℤ) then acc + 2 else acc + 1
    let L : Nat := Array.foldl f 0 (arr.extract 0 idx) 0 (min idx arr.size)
    let Lm1 : Nat := Array.foldl f 0 (arr.extract 0 (idx - 1)) 0 (min (idx - 1) arr.size)

    have hidxne0 : idx ≠ 0 := Nat.ne_of_gt if_pos
    have hsub_lt : idx - 1 < idx := by
      -- turn `idx - 1` into `Nat.pred idx`
      rw [Nat.sub_one]
      exact Nat.pred_lt hidxne0
    have hlt : idx - 1 < arr.size :=
      Nat.lt_of_lt_of_le hsub_lt invariant_dz_pass2_idx_le_n
    have hle : idx - 1 ≤ arr.size :=
      Nat.le_trans (Nat.sub_le idx 1) invariant_dz_pass2_idx_le_n

    have hsub_add : idx - 1 + 1 = idx :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt if_pos)

    have hEq : Lm1 + 2 = L := by
      -- instantiate the "+2" produced-length update for a zero element
      simpa [Lm1, L, f, hsub_add] using
        (goal_0 (arr := arr) (i := idx - 1)
          (invariant_dz_pass1_i_le_n := hle) (if_pos := hlt) (if_pos_1 := if_pos_1))

    have h2 : 2 ≤ Lm1 + 2 := Nat.le_add_left 2 Lm1

    have hLge2 : 2 ≤ L := by
      simpa [hEq] using h2

    have hLle1 : L ≤ 1 := by
      simpa [L, f] using if_neg

    have h21 : 2 ≤ 1 := Nat.le_trans hLge2 hLle1
    have : Nat.succ 1 ≤ 1 := by simpa using h21
    exact Nat.not_succ_le_self 1 this

  exact False.elim hFalse

theorem goal_6
    (arr : Array ℤ)
    (idx : ℕ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    intros; expose_names; exact goal_2 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos

theorem goal_7
    (arr : Array ℤ)
    (idx : ℕ)
    (res : Array ℤ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (invariant_dz_pass2_res_size : res.size = arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    (if_pos_2 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size))
    (if_neg : arr.size ≤ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1)
    (if_pos_4 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1 < arr.size)
    : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j + OfNat.ofNat 1 + OfNat.ofNat 1 → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (res.setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1) (OfNat.ofNat 0))[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
  intro j hj hwp_le
  classical

  let prod : Nat → Nat := fun k =>
    Array.foldl (fun acc x => if x = (0 : ℤ) then acc + 2 else acc + 1) (0 : Nat)
      (arr.extract 0 k) 0 (min k arr.size)
  set wp : Nat := prod idx with hwp

  have hwp_pos : 0 < wp := by
    simpa [wp, prod] using if_pos_2

  have h1le : 1 ≤ wp := Nat.succ_le_of_lt hwp_pos

  have if_neg' : arr.size ≤ wp - 1 := by
    simpa [wp, prod] using if_neg

  have hn1_le_wp : arr.size + 1 ≤ wp := by
    have h : arr.size + 1 ≤ (wp - 1) + 1 := Nat.add_le_add_right if_neg' 1
    -- cancel (wp-1)+1 = wp
    simpa [Nat.sub_add_cancel h1le] using h

  have hj2_le : j + 2 ≤ arr.size + 1 := by
    have hlt : j + 2 < arr.size + 2 := Nat.add_lt_add_right hj 2
    exact (Nat.lt_succ_iff.mp (by
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlt))

  have hwp_le_n1 : wp ≤ arr.size + 1 := le_trans (by simpa [wp] using hwp_le) hj2_le

  have hwp_eq : wp = arr.size + 1 := Nat.le_antisymm hwp_le_n1 hn1_le_wp

  have hwp_eq' : wp = j + 2 := by
    apply Nat.le_antisymm
    · exact (by simpa [wp] using hwp_le)
    · simpa [hwp_eq] using hj2_le

  have hj_lt_wp : j < wp := by
    have : j < j + 2 := Nat.lt_add_of_pos_right (n := j) (k := 2) (by decide : 0 < 2)
    simpa [hwp_eq'] using this

  have hj_eq_wp2 : j = wp - 1 - 1 := by
    have hwpsub : wp - 2 = j := by
      calc
        wp - 2 = (j + 2) - 2 := by simpa [hwp_eq']
        _ = j := by simpa using (Nat.add_sub_cancel j 2)
    simpa [Nat.sub_sub, Nat.add_assoc] using hwpsub.symm

  have hwp2_lt_res : wp - 1 - 1 < res.size := by
    have hwp2_lt_n : wp - 1 - 1 < arr.size := by
      simpa [wp, prod] using if_pos_4
    simpa [invariant_dz_pass2_res_size] using hwp2_lt_n

  have hwp2_eq_prod_pred : wp - 1 - 1 = prod (idx - 1) := by
    simpa [wp, prod] using goal_6 arr idx invariant_dz_pass2_idx_le_n if_pos_1 (by simpa using if_pos)

  have hidx_pred_lt : idx - 1 < arr.size := by
    have hne : idx ≠ 0 := Nat.ne_of_gt (by simpa using if_pos)
    have hlt : idx - 1 < idx := Nat.sub_one_lt hne
    exact lt_of_lt_of_le hlt invariant_dz_pass2_idx_le_n

  have hidx_pred_add_one : idx - 1 + 1 = idx :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (by simpa using if_pos))

  -- Strict increase of prod at each step within bounds
  have prod_succ_lt : ∀ k, k < arr.size → prod k < prod (k + 1) := by
    intro k hk
    by_cases hz : arr[k]! = (0 : ℤ)
    · have hEq := goal_0 arr k (le_of_lt hk) hk (by simpa using hz)
      have : prod k < prod k + 2 :=
        Nat.lt_add_of_pos_right (n := prod k) (k := 2) (by decide : 0 < 2)
      simpa [prod, hEq] using this
    · have hEq := goal_1 arr k (le_of_lt hk) hk (by simpa using hz)
      have : prod k < prod k + 1 := by
        simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_self (prod k))
      simpa [prod, hEq] using this

  -- Monotonicity of prod on indices ≤ arr.size
  have prod_mono : ∀ {a b}, a ≤ b → b ≤ arr.size → prod a ≤ prod b := by
    intro a b hab hb
    let P : Nat → Prop := fun m => m ≤ b → prod a ≤ prod m
    have hPa : P a := by
      intro _
      exact le_rfl
    have hstep : ∀ m, a ≤ m → P m → P (m + 1) := by
      intro m ham hPm hm1_le_b
      have hm_le_b : m ≤ b := Nat.le_trans (Nat.le_succ m) hm1_le_b
      have ih : prod a ≤ prod m := hPm hm_le_b
      have hm_lt_n : m < arr.size := by
        have hm1_le_n : m + 1 ≤ arr.size := Nat.le_trans hm1_le_b hb
        exact lt_of_lt_of_le (Nat.lt_succ_self m) hm1_le_n
      have hm_le : prod m ≤ prod (m + 1) := le_of_lt (prod_succ_lt m hm_lt_n)
      exact le_trans ih hm_le
    have hPb : P b := Nat.le_induction hPa hstep b hab
    exact hPb le_rfl

  refine ⟨idx - 1, ?_, ?_⟩
  · refine ⟨hidx_pred_lt, ?_, ?_, ?_⟩
    · -- prod (idx-1) ≤ j
      change prod (idx - 1) ≤ j
      have hprod_eq_j : prod (idx - 1) = j := by
        calc
          prod (idx - 1) = wp - 1 - 1 := by simpa [hwp2_eq_prod_pred]
          _ = j := by simpa [hj_eq_wp2]
      simpa [hprod_eq_j]
    · -- j < prod ((idx-1)+1)
      change j < prod (idx - 1 + 1)
      have hprod_succ : prod (idx - 1 + 1) = wp := by
        simp [wp, hidx_pred_add_one]
      simpa [hprod_succ] using hj_lt_wp
    · -- value equation
      have harr0 : arr[idx - 1]! = (0 : ℤ) := by simpa using if_pos_1
      have hget : (res.setIfInBounds (wp - 1 - 1) (0 : ℤ))[wp - 1 - 1]! = (0 : ℤ) := by
        simp [Array.get!_eq_getD_getElem?, Array.getElem?_setIfInBounds, hwp2_lt_res]
      simpa [hj_eq_wp2, harr0, hget]
  · intro y hy
    have hy_lt : y < arr.size := hy.1
    have hy_le : prod y ≤ j := hy.2.1
    have hj_lt : j < prod (y + 1) := hy.2.2.1
    have htri := Nat.lt_trichotomy y (idx - 1)
    cases htri with
    | inl hlt =>
        have hy1_le : y + 1 ≤ idx - 1 := Nat.succ_le_of_lt hlt
        have hmono : prod (y + 1) ≤ prod (idx - 1) :=
          prod_mono hy1_le (le_of_lt hidx_pred_lt)
        have hEqj : prod (idx - 1) = j := by
          calc
            prod (idx - 1) = wp - 1 - 1 := by simpa [hwp2_eq_prod_pred]
            _ = j := by simpa [hj_eq_wp2]
        have : prod (y + 1) ≤ j := by simpa [hEqj] using hmono
        exact (False.elim (Nat.not_lt_of_ge this hj_lt))
    | inr hge =>
        cases hge with
        | inl heq =>
            simpa [heq]
        | inr hgt =>
            have hidx_le_y : idx ≤ y := by
              have : idx - 1 + 1 ≤ y := Nat.succ_le_of_lt hgt
              simpa [hidx_pred_add_one] using this
            have hmono : prod idx ≤ prod y :=
              prod_mono hidx_le_y (le_of_lt hy_lt)
            have hwp_gt_j : j < prod idx := by
              simpa [wp] using hj_lt_wp
            have : j < prod y := lt_of_lt_of_le hwp_gt_j hmono
            exact (False.elim (Nat.not_lt_of_ge hy_le this))

theorem goal_8
    (arr : Array ℤ)
    (idx : ℕ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    intros; expose_names; exact goal_6 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos

theorem goal_9
    (arr : Array ℤ)
    (idx : ℕ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_pos_1 : arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    (if_neg : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = OfNat.ofNat 0)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
  classical
  -- Name the repeated fold expressions.
  set t : Nat :=
    Array.foldl
      (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
      (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size)
  set u : Nat :=
    Array.foldl
      (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
      (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0)
      (min (idx - OfNat.ofNat 1) arr.size)

  have ht0 : t = OfNat.ofNat 0 := by
    simpa [t] using if_neg

  have hu0 : u = OfNat.ofNat 0 := by
    have hstep :=
      goal_8 (arr := arr) (idx := idx) invariant_dz_pass2_idx_le_n if_pos_1 if_pos
    -- Rewrite hstep in terms of t and u, then use ht0.
    have hstep' : t - OfNat.ofNat 1 - OfNat.ofNat 1 = u := by
      simpa [t, u] using hstep
    have hstep'' := hstep'
    rw [ht0] at hstep''
    have : (OfNat.ofNat 0 : Nat) = u := by
      simpa using hstep''
    exact this.symm

  have : t = u := by
    calc
      t = OfNat.ofNat 0 := ht0
      _ = u := by
        simpa using hu0.symm

  simpa [t, u] using this

theorem goal_10
    (arr : Array ℤ)
    (idx : ℕ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (if_pos : OfNat.ofNat 0 < idx)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
  classical
  -- Abbreviate the produced-length fold over the prefix `k`.
  let F (k : Nat) : Nat :=
    Array.foldl
      (fun acc x => if x = (0 : Int) then acc + 2 else acc + 1)
      0
      (arr.extract 0 k)
      0
      (min k arr.size)

  have hposIdx : idx ≠ 0 := Nat.ne_of_gt if_pos

  have hlt_idx : idx - 1 < idx := by
    have : idx - 1 < Nat.succ (idx - 1) := Nat.lt_succ_self (idx - 1)
    simpa [Nat.succ_eq_add_one, Nat.sub_one_add_one hposIdx] using this

  have hi_lt : idx - 1 < arr.size :=
    lt_of_lt_of_le hlt_idx invariant_dz_pass2_idx_le_n

  have hi_le : idx - 1 ≤ arr.size :=
    le_trans (Nat.sub_le idx 1) invariant_dz_pass2_idx_le_n

  have hstep : F (idx - 1) + 1 = F idx := by
    -- Use the one-step fold lemma for the nonzero case.
    have h :=
      goal_1
        (arr := arr)
        (i := idx - 1)
        hi_le
        hi_lt
        (by
          -- rewrite `OfNat.ofNat` numerals
          simpa using if_neg)
    -- Rewrite `(idx - 1) + 1` to `idx`.
    simpa [F, Nat.sub_one_add_one hposIdx, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

  have hF : F idx = F (idx - 1) + 1 := by
    simpa using hstep.symm

  -- Now subtract 1 from both sides.
  calc
    Array.foldl
          (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0)
          (arr.extract (OfNat.ofNat 0) idx)
          (OfNat.ofNat 0)
          (min idx arr.size)
          - OfNat.ofNat 1
        = F idx - 1 := by
            simp [F]
    _ = (F (idx - 1) + 1) - 1 := by
          simp [hF]
    _ = F (idx - 1) := by
          simp
    _ = Array.foldl
          (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1)
          (OfNat.ofNat 0)
          (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1))
          (OfNat.ofNat 0)
          (min (idx - OfNat.ofNat 1) arr.size) := by
          simp [F]



theorem goal_11
    (arr : Array ℤ)
    (require_1 : True)
    (i_1 : ℕ)
    (idx : ℕ)
    (res : Array ℤ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (invariant_dz_pass2_res_size : res.size = arr.size)
    (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size)
    (if_pos : OfNat.ofNat 0 < idx)
    (done_1 : arr.size ≤ i_1)
    (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!)
    (if_pos_1 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size))
    (if_pos_2 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 < arr.size)
    : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j + OfNat.ofNat 1 → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (res.setIfInBounds (Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1) arr[idx - OfNat.ofNat 1]!)[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
    sorry

theorem goal_12
    (arr : Array ℤ)
    (require_1 : True)
    (i_1 : ℕ)
    (idx : ℕ)
    (res : Array ℤ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (invariant_dz_pass2_res_size : res.size = arr.size)
    (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size)
    (if_pos : OfNat.ofNat 0 < idx)
    (done_1 : arr.size ≤ i_1)
    (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!)
    (if_pos_1 : OfNat.ofNat 0 < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size))
    (if_neg_1 : arr.size ≤ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) - OfNat.ofNat 1 = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    sorry

theorem goal_13
    (arr : Array ℤ)
    (require_1 : True)
    (i_1 : ℕ)
    (idx : ℕ)
    (res : Array ℤ)
    (invariant_dz_pass2_idx_le_n : idx ≤ arr.size)
    (invariant_dz_pass2_res_size : res.size = arr.size)
    (if_neg : ¬arr[idx - OfNat.ofNat 1]! = OfNat.ofNat 0)
    (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size)
    (if_pos : OfNat.ofNat 0 < idx)
    (done_1 : arr.size ≤ i_1)
    (invariant_dz_pass2_suffix_correct : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ res[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]!)
    (if_neg_1 : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = OfNat.ofNat 0)
    : Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) idx) (OfNat.ofNat 0) (min idx arr.size) = Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (idx - OfNat.ofNat 1)) (OfNat.ofNat 0) (min (idx - OfNat.ofNat 1) arr.size) := by
    sorry

theorem goal_14
    (arr : Array ℤ)
    (require_1 : True)
    (i_1 : ℕ)
    (invariant_dz_pass1_i_le_n : i_1 ≤ arr.size)
    (done_1 : arr.size ≤ i_1)
    : ∀ j < arr.size, Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 arr.size) ≤ j → ∃! i, i < arr.size ∧ Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i arr.size) ≤ j ∧ j < Array.foldl (fun acc x => if x = OfNat.ofNat 0 then acc + OfNat.ofNat 2 else acc + OfNat.ofNat 1) (OfNat.ofNat 0) (arr.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) arr.size) ∧ (Array.replicate arr.size (OfNat.ofNat 0))[j]! = if arr[i]! = OfNat.ofNat 0 then OfNat.ofNat 0 else arr[i]! := by
    sorry



prove_correct DuplicateZeros by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 arr i invariant_dz_pass1_i_le_n if_pos if_pos_1)
  exact (goal_1 arr i invariant_dz_pass1_i_le_n if_pos if_neg)
  exact (goal_2 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos)
  exact (goal_3 arr i_1 idx res invariant_dz_pass2_idx_le_n invariant_dz_pass2_res_size if_pos_1 invariant_dz_pass1_i_le_n if_pos done_1 invariant_dz_pass2_suffix_correct if_pos_2 if_pos_3 if_pos_4 if_pos_5)
  exact (goal_4 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos if_pos_2 if_neg)
  exact (goal_5 arr i_1 idx res invariant_dz_pass2_idx_le_n if_pos_1 invariant_dz_pass1_i_le_n if_pos if_neg)
  exact (goal_6 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos)
  exact (goal_7 arr idx res invariant_dz_pass2_idx_le_n invariant_dz_pass2_res_size if_pos_1 if_pos if_pos_2 if_neg if_pos_4)
  exact (goal_8 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos)
  exact (goal_9 arr idx invariant_dz_pass2_idx_le_n if_pos_1 if_pos if_neg)
  exact (goal_10 arr idx invariant_dz_pass2_idx_le_n if_neg if_pos)
  exact (goal_11 arr require_1 i_1 idx res invariant_dz_pass2_idx_le_n invariant_dz_pass2_res_size if_neg invariant_dz_pass1_i_le_n if_pos done_1 invariant_dz_pass2_suffix_correct if_pos_1 if_pos_2)
  exact (goal_12 arr require_1 i_1 idx res invariant_dz_pass2_idx_le_n invariant_dz_pass2_res_size if_neg invariant_dz_pass1_i_le_n if_pos done_1 invariant_dz_pass2_suffix_correct if_pos_1 if_neg_1)
  exact (goal_13 arr require_1 i_1 idx res invariant_dz_pass2_idx_le_n invariant_dz_pass2_res_size if_neg invariant_dz_pass1_i_le_n if_pos done_1 invariant_dz_pass2_suffix_correct if_neg_1)
  exact (goal_14 arr require_1 i_1 invariant_dz_pass1_i_le_n done_1)
end Proof
