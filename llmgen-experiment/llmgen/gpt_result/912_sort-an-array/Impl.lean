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
    SortAnArray: Given an array of integers, return the same elements sorted in ascending (nondecreasing) order.
    **Important: complexity should be O(n + k) time and O(k) space, where k is the range of values**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. The output is an array of integers with the same length as `nums`.
    3. The output must be sorted in nondecreasing order (ascending with duplicates allowed).
    4. The output must be a permutation of the input: every integer value occurs the same number of times in the output as in the input.
    5. Constraints: 1 ≤ nums.length ≤ 5 * 10^4.
    6. Constraints: each element nums[i] satisfies -5 * 10^4 ≤ nums[i] ≤ 5 * 10^4.
-/

section Specs
-- The allowed value range from the problem constraints.
def minVal : Int := -50000

def maxVal : Int := 50000

-- Array is sorted in nondecreasing order.
def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- All elements satisfy the given inclusive bounds.
def allInRange (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size → minVal ≤ arr[i]! ∧ arr[i]! ≤ maxVal

-- Input constraints from the problem statement.
def precondition (nums : Array Int) : Prop :=
  allInRange nums

-- Output requirements: same length, sorted, stays within the required bounds,
-- and has exactly the same multiplicities as the input for every Int value.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  isSortedNondecreasing result ∧
  allInRange result ∧
  (∀ (v : Int), result.count v = nums.count v)
end Specs

section Impl
method SortAnArray (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Counting sort over the fixed range [minVal, maxVal].
  let kNat : Nat := Int.toNat (maxVal - minVal + 1)
  let mut counts : Array Nat := Array.replicate kNat 0

  -- Count occurrences.
  let mut i : Nat := 0
  while i < nums.size
    -- counts has fixed size
    invariant "cnt_size" counts.size = kNat
    -- i stays within bounds
    invariant "cnt_i_le" i ≤ nums.size
    -- histogram for processed prefix of nums
    invariant "cnt_hist" (∀ v : Int, minVal ≤ v ∧ v ≤ maxVal →
      counts[Int.toNat (v - minVal)]! = (nums.extract 0 i).count v)
    -- total number of counted elements equals i
    invariant "cnt_sum" counts.foldl (fun s x => s + x) 0 = i
    decreasing nums.size - i
  do
    let v : Int := nums[i]!
    -- v is in range by precondition; map it to [0, kNat).
    let idx : Nat := Int.toNat (v - minVal)
    counts := counts.set! idx (counts[idx]! + 1)
    i := i + 1

  -- Reconstruct sorted output.
  let mut out : Array Int := Array.replicate nums.size 0
  let mut outPos : Nat := 0
  let mut cIdx : Nat := 0
  while cIdx < kNat
    -- sizes stay fixed
    invariant "rec_counts_size" counts.size = kNat
    invariant "rec_out_size" out.size = nums.size
    -- bounds for indices
    invariant "rec_cIdx_le" cIdx ≤ kNat
    invariant "rec_outPos_le" outPos ≤ out.size
    -- emitted prefix length is sum of counts for finished buckets
    invariant "rec_outPos_def" outPos = (counts.extract 0 cIdx).foldl (fun s x => s + x) 0
    -- emitted prefix is sorted and in range
    invariant "rec_prefix_sorted" isSortedNondecreasing (out.extract 0 outPos)
    invariant "rec_prefix_range" allInRange (out.extract 0 outPos)
    -- counts for values < current bucket are correct in emitted prefix
    invariant "rec_prefix_counts_done" (∀ j : Nat, j < cIdx →
      (out.extract 0 outPos).count (minVal + (Int.ofNat j)) = counts[j]!)
    -- no value greater than the next-to-emit value appears in the prefix
    invariant "rec_prefix_no_large" (∀ v : Int,
      (minVal + (Int.ofNat cIdx)) < v → (out.extract 0 outPos).count v = 0)
    decreasing kNat - cIdx
  do
    let mut remaining : Nat := counts[cIdx]!
    while remaining > 0
      invariant "in_out_size" out.size = nums.size
      invariant "in_counts_size" counts.size = kNat
      invariant "in_cIdx_lt" cIdx < kNat
      invariant "in_outPos_le" outPos ≤ out.size
      -- outPos includes finished buckets (< cIdx) plus already-written of current bucket
      invariant "in_outPos_def" outPos = (counts.extract 0 cIdx).foldl (fun s x => s + x) 0 + (counts[cIdx]! - remaining)
      invariant "in_remaining_le" remaining ≤ counts[cIdx]!
      -- enough space left to write the remaining occurrences of current value
      invariant "in_space" outPos + remaining ≤ out.size
      -- emitted prefix is sorted and in range
      invariant "in_prefix_sorted" isSortedNondecreasing (out.extract 0 outPos)
      invariant "in_prefix_range" allInRange (out.extract 0 outPos)
      -- finished buckets remain correct in the emitted prefix
      invariant "in_prefix_counts_done" (∀ j : Nat, j < cIdx →
        (out.extract 0 outPos).count (minVal + (Int.ofNat j)) = counts[j]!)
      -- current bucket count in emitted prefix matches how many we've written so far
      invariant "in_prefix_counts_cur" (out.extract 0 outPos).count (minVal + (Int.ofNat cIdx)) = counts[cIdx]! - remaining
      -- no value greater than the current bucket value appears in the prefix
      invariant "in_prefix_no_large" (∀ v : Int,
        (minVal + (Int.ofNat cIdx)) < v → (out.extract 0 outPos).count v = 0)
      decreasing remaining
    do
      let value : Int := minVal + (Int.ofNat cIdx)
      out := out.set! outPos value
      outPos := outPos + 1
      remaining := remaining - 1
    cIdx := cIdx + 1

  return out
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [5,2,3,1]
-- Output: [1,2,3,5]
def test1_nums : Array Int := #[5, 2, 3, 1]
def test1_Expected : Array Int := #[1, 2, 3, 5]

-- Test case 2: Example 2 with duplicates
-- Input: [5,1,1,2,0,0]
-- Output: [0,0,1,1,2,5]
def test2_nums : Array Int := #[5, 1, 1, 2, 0, 0]
def test2_Expected : Array Int := #[0, 0, 1, 1, 2, 5]

-- Test case 3: Single element (boundary size)
def test3_nums : Array Int := #[42]
def test3_Expected : Array Int := #[42]

-- Test case 4: Already sorted array (includes negatives and 0)
def test4_nums : Array Int := #[-3, -1, 0, 2, 4]
def test4_Expected : Array Int := #[-3, -1, 0, 2, 4]

-- Test case 5: Reverse sorted array
def test5_nums : Array Int := #[4, 3, 2, 1, 0]
def test5_Expected : Array Int := #[0, 1, 2, 3, 4]

-- Test case 6: All elements equal
def test6_nums : Array Int := #[7, 7, 7, 7]
def test6_Expected : Array Int := #[7, 7, 7, 7]

-- Test case 7: Includes negative numbers and duplicates
def test7_nums : Array Int := #[-1, -5, -1, 3, 0, -5]
def test7_Expected : Array Int := #[-5, -5, -1, -1, 0, 3]

-- Test case 8: Includes min/max constraint boundaries
def test8_nums : Array Int := #[50000, -50000, 0, 50000, -50000]
def test8_Expected : Array Int := #[-50000, -50000, 0, 50000, 50000]

-- Test case 9: Mixed values with repeated zeros
def test9_nums : Array Int := #[0, 2, 0, 1, 2, 0]
def test9_Expected : Array Int := #[0, 0, 0, 1, 2, 2]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((SortAnArray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SortAnArray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SortAnArray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SortAnArray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SortAnArray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SortAnArray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SortAnArray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SortAnArray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SortAnArray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test SortAnArray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (counts : Array ℕ)
    (if_pos : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts < nums.size)
    (invariant_cnt_size : counts.size = OfNat.ofNat 100001)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → counts[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts)))
    : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → (counts.setIfInBounds (nums[Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts]! + OfNat.ofNat 50000).toNat (counts[(nums[Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1))[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts + OfNat.ofNat 1)) := by
  intro v hvLo hvHi

  set i : Nat := Array.foldl (fun s x => s + x) 0 counts with hiDef
  have hi : i < nums.size := by
    simpa [i] using if_pos
  have hi' : i < nums.size := hi

  set x : ℤ := nums[i]! with hxDef
  have hxRange : (-50000 : ℤ) ≤ x ∧ x ≤ (50000 : ℤ) := by
    simpa [x] using require_1 i hi
  have hxLo : (-50000 : ℤ) ≤ x := hxRange.1
  have hxHi : x ≤ (50000 : ℤ) := hxRange.2

  have hxBang : nums[i]! = nums[i]'hi' := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, hi']
  have hxEq : nums[i]'hi' = x := by
    calc
      nums[i]'hi' = nums[i]! := by simpa using hxBang.symm
      _ = x := by simpa [hxDef]

  set idx : Nat := (x + 50000).toNat with hidxDef
  set j : Nat := (v + 50000).toNat with hjDef

  have hxNonneg : (0 : ℤ) ≤ x + 50000 := by omega

  have hidx_lt : idx < counts.size := by
    have hxLe : x + 50000 ≤ (100000 : ℤ) := by omega
    have hidx_le : idx ≤ 100000 := by
      have hidxInt : (idx : ℤ) = x + 50000 := by
        simp [idx, Int.toNat_of_nonneg hxNonneg]
      have : (idx : ℤ) ≤ (100000 : ℤ) := by simpa [hidxInt] using hxLe
      exact_mod_cast this
    have : idx < 100001 := Nat.lt_of_le_of_lt hidx_le (by decide)
    simpa [invariant_cnt_size] using this

  have hextract : (nums.extract 0 i).push x = nums.extract 0 (i + 1) := by
    have h0 : (nums.extract 0 i).push (nums[i]'hi') = nums.extract 0 (i + 1) := by
      simpa using (@Array.push_extract_getElem ℤ nums 0 i hi')
    simpa [hxEq] using h0

  have hx_mem : counts[(x + 50000).toNat]! = Array.count x (nums.extract 0 i) := by
    simpa [i] using invariant_cnt_hist x hxLo hxHi

  have hv_mem : counts[(v + 50000).toNat]! = Array.count v (nums.extract 0 i) := by
    simpa [i] using invariant_cnt_hist v hvLo hvHi

  by_cases hvx : v = x
  · subst hvx

    have hget : (counts.setIfInBounds idx (counts[idx]! + 1))[idx]! = counts[idx]! + 1 := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hidx_lt]

    have hcount : Array.count x (nums.extract 0 (i + 1)) = Array.count x (nums.extract 0 i) + 1 := by
      have hpush : Array.count x ((nums.extract 0 i).push x) = Array.count x (nums.extract 0 i) + 1 :=
        Array.count_push_self (a := x) (xs := nums.extract 0 i)
      simpa [hextract] using hpush

    have hidx0 : (nums[i]! + 50000).toNat = idx := by
      simp [idx, hxDef]

    have hrepl :
        (counts.setIfInBounds (nums[i]! + 50000).toNat (counts[(nums[i]! + 50000).toNat]! + 1))[(x + 50000).toNat]!
          = (counts.setIfInBounds idx (counts[idx]! + 1))[idx]! := by
      rw [hidx0]

    calc
      (counts.setIfInBounds (nums[i]! + 50000).toNat (counts[(nums[i]! + 50000).toNat]! + 1))[(x + 50000).toNat]!
          = (counts.setIfInBounds idx (counts[idx]! + 1))[idx]! := hrepl
      _ = counts[idx]! + 1 := hget
      _ = Array.count x (nums.extract 0 i) + 1 := by
            simpa [idx] using congrArg (fun n => n) hx_mem
      _ = Array.count x (nums.extract 0 (i + 1)) := by
            simpa [hcount]

  ·
    have hvLo' : (-50000 : ℤ) ≤ v := by simpa using hvLo
    have hvNonneg : (0 : ℤ) ≤ v + 50000 := by omega

    have hneIdx : idx ≠ j := by
      intro hEq
      have hEqInt : (idx : ℤ) = (j : ℤ) := congrArg (fun n : Nat => (n : ℤ)) hEq
      have : x + 50000 = v + 50000 := by
        simpa [idx, j, Int.toNat_of_nonneg hxNonneg, Int.toNat_of_nonneg hvNonneg] using hEqInt
      have : x = v := by omega
      exact hvx this.symm

    have hget : (counts.setIfInBounds idx (counts[idx]! + 1))[j]! = counts[j]! := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hneIdx]

    have hcount : Array.count v (nums.extract 0 (i + 1)) = Array.count v (nums.extract 0 i) := by
      have hxne : x ≠ v := by simpa [ne_comm] using hvx
      have hpush : Array.count v ((nums.extract 0 i).push x) = Array.count v (nums.extract 0 i) :=
        Array.count_push_of_ne (a := v) (b := x) (xs := nums.extract 0 i) hxne
      simpa [hextract] using hpush

    have hidx0 : (nums[i]! + 50000).toNat = idx := by
      simp [idx, hxDef]

    have hrepl :
        (counts.setIfInBounds (nums[i]! + 50000).toNat (counts[(nums[i]! + 50000).toNat]! + 1))[(v + 50000).toNat]!
          = (counts.setIfInBounds idx (counts[idx]! + 1))[j]! := by
      rw [hidx0]

    calc
      (counts.setIfInBounds (nums[i]! + 50000).toNat (counts[(nums[i]! + 50000).toNat]! + 1))[(v + 50000).toNat]!
          = (counts.setIfInBounds idx (counts[idx]! + 1))[j]! := hrepl
      _ = counts[j]! := hget
      _ = Array.count v (nums.extract 0 i) := by
          simpa [j] using hv_mem
      _ = Array.count v (nums.extract 0 (i + 1)) := by
          simpa [hcount]

lemma List.foldl_add_add (l : List Nat) (b c : Nat) :
    l.foldl (fun s x => s + x) (b + c) = l.foldl (fun s x => s + x) b + c := by
  induction l generalizing b with
  | nil => simp
  | cons a t ih =>
      have hinit : (b + c) + a = (b + a) + c := by
        ac_rfl
      -- unfold one step of foldl and use the induction hypothesis
      simpa [List.foldl, hinit] using (ih (b := b + a))

lemma List.foldl_add_set_get_succ (l : List Nat) (i : Nat) (b : Nat) (h : i < l.length) :
    (l.set i (l.get ⟨i, h⟩ + 1)).foldl (fun s x => s + x) b =
      l.foldl (fun s x => s + x) b + 1 := by
  induction l generalizing i b with
  | nil => cases h
  | cons a t ih =>
      cases i with
      | zero =>
          -- update the head
          -- goal reduces to shifting the initial accumulator by 1
          simpa [List.set, List.get, List.foldl, Nat.add_assoc] using
            (List.foldl_add_add (l := t) (b := b + a) (c := 1))
      | succ i =>
          have h' : i < t.length := Nat.lt_of_succ_lt_succ h
          -- update in the tail
          simpa [List.set, List.get, List.foldl, h', Nat.add_assoc] using
            (ih (i := i) (b := b + a) h')


theorem goal_1
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (counts : Array ℕ)
    (if_pos : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts < nums.size)
    (invariant_cnt_size : counts.size = OfNat.ofNat 100001)
    : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (counts.setIfInBounds (nums[Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts]! + OfNat.ofNat 50000).toNat (counts[(nums[Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts]! + OfNat.ofNat 50000).toNat]! + OfNat.ofNat 1)) (OfNat.ofNat 0) counts.size = Array.foldl (fun s x => s + x) (OfNat.ofNat 0) counts + OfNat.ofNat 1 := by
  classical

  -- abbreviate the current total count
  set k : Nat := Array.foldl (fun s x => s + x) 0 counts with hk
  have hk' : k < nums.size := by
    simpa [k] using if_pos

  have hxRange : (-50000 : ℤ) ≤ nums[k]! ∧ nums[k]! ≤ (50000 : ℤ) := by
    simpa using (require_1 k hk')

  set idx : Nat := (nums[k]! + (50000 : ℤ)).toNat with hidx_def

  -- show idx < counts.size (so the histogram index is in bounds)
  have hnonneg : (0 : ℤ) ≤ nums[k]! + (50000 : ℤ) := by
    have h : (-50000 : ℤ) ≤ nums[k]! := hxRange.1
    omega
  have hle : nums[k]! + (50000 : ℤ) ≤ (100000 : ℤ) := by
    have h : nums[k]! ≤ (50000 : ℤ) := hxRange.2
    omega

  have hidx_le : idx ≤ 100000 := by
    have hidx_int : (idx : ℤ) = nums[k]! + (50000 : ℤ) := by
      simpa [idx] using (Int.toNat_of_nonneg hnonneg)
    have : (idx : ℤ) ≤ (100000 : ℤ) := by
      simpa [hidx_int] using hle
    exact Int.ofNat_le.mp this

  have hidx_lt : idx < 100001 := by
    have : idx < Nat.succ 100000 := Nat.lt_succ_of_le hidx_le
    simpa using this

  have hidx : idx < counts.size := by
    simpa [invariant_cnt_size] using hidx_lt

  -- rewrite the goal using k and idx
  simp [k, hk, idx, hidx_def]

  -- switch to lists to reason about foldl and set
  let updated : Array Nat := counts.setIfInBounds idx (counts[idx]! + 1)

  have hstop : counts.size = updated.toList.toArray.size := by
    have : updated.size = counts.size := by
      simp [updated, Array.size_setIfInBounds]
    simpa [List.size_toArray, Array.length_toList, this]

  have hLHS_toList :
      Array.foldl (fun s x => s + x) 0 updated 0 counts.size =
        updated.toList.foldl (fun s x => s + x) 0 := by
    have h :=
      (List.foldl_toArray' (stop := counts.size) (fun s x : Nat => s + x) 0 updated.toList hstop)
    simpa using h

  have hRHS_toList :
      Array.foldl (fun s x => s + x) 0 counts =
        counts.toList.foldl (fun s x => s + x) 0 := by
    simpa using
      (Array.foldl_eq_foldl_toList (f := fun s x : Nat => s + x) (init := 0) (xs := counts))

  have hlen : idx < counts.toList.length := by
    simpa [Array.length_toList] using hidx

  -- in-bounds, safe indexing and `!` coincide
  have hidxSafe : counts[idx] = counts[idx]! := by
    simp [hidx]

  have hlist :
      (counts.toList.set idx (counts[idx]! + 1)).foldl (fun s x => s + x) 0 =
        counts.toList.foldl (fun s x => s + x) 0 + 1 := by
    -- List.get on counts.toList simplifies to the safe array indexing counts[idx]
    -- then use hidxSafe to turn it into counts[idx]!
    simpa [hidxSafe] using
      (List.foldl_add_set_get_succ (l := counts.toList) (i := idx) (b := 0) hlen)

  have hUpdated_toList : updated.toList = counts.toList.set idx (counts[idx]! + 1) := by
    simp [updated, Array.toList_setIfInBounds]

  -- finish by rewriting both sides via toList
  calc
    Array.foldl (fun s x => s + x) 0 updated 0 counts.size
        = updated.toList.foldl (fun s x => s + x) 0 := hLHS_toList
    _ = (counts.toList.set idx (counts[idx]! + 1)).foldl (fun s x => s + x) 0 := by
          simpa [hUpdated_toList]
    _ = counts.toList.foldl (fun s x => s + x) 0 + 1 := hlist
    _ = Array.foldl (fun s x => s + x) 0 counts + 1 := by
          simpa using congrArg (fun t => t + 1) (Eq.symm hRHS_toList)


theorem goal_2
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (Array.replicate (OfNat.ofNat 100001) (OfNat.ofNat 0)) (OfNat.ofNat 0) (OfNat.ofNat 100001) = OfNat.ofNat 0 := by
    sorry

theorem goal_3
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (out_1 : Array ℤ)
    (remaining : ℕ)
    (invariant_in_out_size : out_1.size = nums.size)
    (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001)
    (if_pos_1 : OfNat.ofNat 0 < remaining)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size)
    (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size)
    (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!)
    (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!)
    (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining)
    (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0)
    : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1 → j < out_1.size → ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ≤ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[j]! := by
    sorry

theorem goal_4
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (out_1 : Array ℤ)
    (remaining : ℕ)
    (invariant_in_out_size : out_1.size = nums.size)
    (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001)
    (if_pos_1 : OfNat.ofNat 0 < remaining)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size)
    (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size)
    (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!)
    (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!)
    (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining)
    (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0)
    : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1, i < out_1.size → -OfNat.ofNat 50000 ≤ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ∧ ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1))[i]! ≤ OfNat.ofNat 50000 := by
    sorry

theorem goal_5
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (out_1 : Array ℤ)
    (remaining : ℕ)
    (invariant_in_out_size : out_1.size = nums.size)
    (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001)
    (if_pos_1 : OfNat.ofNat 0 < remaining)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size)
    (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size)
    (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!)
    (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!)
    (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining)
    (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0)
    : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = i_1[j]! := by
    sorry

theorem goal_6
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (out_1 : Array ℤ)
    (remaining : ℕ)
    (invariant_in_out_size : out_1.size = nums.size)
    (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001)
    (if_pos_1 : OfNat.ofNat 0 < remaining)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size)
    (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size)
    (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!)
    (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!)
    (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining)
    (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0)
    : Array.count (-OfNat.ofNat 50000 + cIdx.cast) ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = i_1[cIdx]! - (remaining - OfNat.ofNat 1) := by
    sorry

theorem goal_7
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (out_1 : Array ℤ)
    (remaining : ℕ)
    (invariant_in_out_size : out_1.size = nums.size)
    (invariant_in_remaining_le : remaining ≤ i_1[cIdx]!)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001)
    (if_pos_1 : OfNat.ofNat 0 < remaining)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) ≤ out_1.size)
    (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + remaining ≤ out_1.size)
    (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) → j < out_1.size → (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[j]!)
    (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining), i < out_1.size → -OfNat.ofNat 50000 ≤ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ∧ (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[j]!)
    (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = i_1[cIdx]! - remaining)
    (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out_1.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining))) = OfNat.ofNat 0)
    : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v ((out_1.setIfInBounds (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining)) (-OfNat.ofNat 50000 + cIdx.cast)).extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining) + OfNat.ofNat 1)) = OfNat.ofNat 0 := by
    sorry

theorem goal_8
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + i_1[cIdx]! ≤ out.size := by
    sorry

theorem goal_9
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0 := by
    sorry

theorem goal_10
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (cIdx : ℕ)
    (out : Array ℤ)
    (invariant_rec_out_size : out.size = nums.size)
    (i_4 : Array ℤ)
    (remaining_1 : ℕ)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_in_out_size : i_4.size = nums.size)
    (invariant_in_remaining_le : remaining_1 ≤ i_1[cIdx]!)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_rec_cIdx_le : cIdx ≤ OfNat.ofNat 100001)
    (if_pos : cIdx < OfNat.ofNat 100001)
    (invariant_in_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_in_cIdx_lt : cIdx < OfNat.ofNat 100001)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) ≤ out.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) → j < out.size → (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size), i < out.size → -OfNat.ofNat 50000 ≤ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ∧ (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (out.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size))) = OfNat.ofNat 0)
    (done_3 : remaining_1 = OfNat.ofNat 0)
    (invariant_in_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) ≤ i_4.size)
    (invariant_in_space : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) + remaining_1 ≤ i_4.size)
    (invariant_in_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) → j < i_4.size → (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ≤ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[j]!)
    (invariant_in_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1), i < i_4.size → -OfNat.ofNat 50000 ≤ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ∧ (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_in_prefix_counts_done : ∀ j < cIdx, Array.count (-OfNat.ofNat 50000 + j.cast) (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = i_1[j]!)
    (invariant_in_prefix_counts_cur : Array.count (-OfNat.ofNat 50000 + cIdx.cast) (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = i_1[cIdx]! - remaining_1)
    (invariant_in_prefix_no_large : ∀ (v : ℤ), cIdx.cast < OfNat.ofNat 50000 + v → Array.count v (i_4.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1))) = OfNat.ofNat 0)
    : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) cIdx) (OfNat.ofNat 0) (min cIdx i_1.size) + (i_1[cIdx]! - remaining_1) = Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) (cIdx + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (cIdx + OfNat.ofNat 1) i_1.size) := by
    sorry

theorem goal_11
    (nums : Array ℤ)
    (require_1 : ∀ i < nums.size, -OfNat.ofNat 50000 ≤ nums[i]! ∧ nums[i]! ≤ OfNat.ofNat 50000)
    (i_1 : Array ℕ)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (invariant_cnt_i_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1 ≤ nums.size)
    (invariant_rec_out_size : i_5.size = nums.size)
    (invariant_rec_counts_size : i_1.size = OfNat.ofNat 100001)
    (invariant_cnt_size : i_1.size = OfNat.ofNat 100001)
    (done_1 : nums.size ≤ Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)
    (invariant_cnt_hist : ∀ (v : ℤ), -OfNat.ofNat 50000 ≤ v → v ≤ OfNat.ofNat 50000 → i_1[(v + OfNat.ofNat 50000).toNat]! = Array.count v (nums.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) i_1)))
    (invariant_rec_cIdx_le : i_4 ≤ OfNat.ofNat 100001)
    (done_2 : OfNat.ofNat 100001 ≤ i_4)
    (invariant_rec_outPos_le : Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size) ≤ i_5.size)
    (invariant_rec_prefix_sorted : ∀ (i j : ℕ), i < j → j < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size) → j < i_5.size → (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ≤ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[j]!)
    (invariant_rec_prefix_range : ∀ i < Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size), i < i_5.size → -OfNat.ofNat 50000 ≤ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ∧ (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size)))[i]! ≤ OfNat.ofNat 50000)
    (invariant_rec_prefix_counts_done : ∀ j < i_4, Array.count (-OfNat.ofNat 50000 + j.cast) (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size))) = i_1[j]!)
    (invariant_rec_prefix_no_large : ∀ (v : ℤ), i_4.cast < OfNat.ofNat 50000 + v → Array.count v (i_5.extract (OfNat.ofNat 0) (Array.foldl (fun s x => s + x) (OfNat.ofNat 0) (i_1.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) (min i_4 i_1.size))) = OfNat.ofNat 0)
    : postcondition nums i_5 := by
    sorry

set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 2)))


set_option maxHeartbeats 10000000


prove_correct SortAnArray by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums require_1 counts invariant_cnt_i_le if_pos invariant_cnt_size invariant_cnt_hist)
  exact (goal_1 nums require_1 counts invariant_cnt_i_le if_pos invariant_cnt_size invariant_cnt_hist)
  exact (goal_2 nums require_1)
  exact (goal_3 nums require_1 i_1 cIdx out invariant_rec_out_size out_1 remaining invariant_in_out_size invariant_in_remaining_le invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_in_counts_size invariant_in_cIdx_lt if_pos_1 invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large invariant_in_outPos_le invariant_in_space invariant_in_prefix_sorted invariant_in_prefix_range invariant_in_prefix_counts_done invariant_in_prefix_counts_cur invariant_in_prefix_no_large)
  exact (goal_4 nums require_1 i_1 cIdx out invariant_rec_out_size out_1 remaining invariant_in_out_size invariant_in_remaining_le invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_in_counts_size invariant_in_cIdx_lt if_pos_1 invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large invariant_in_outPos_le invariant_in_space invariant_in_prefix_sorted invariant_in_prefix_range invariant_in_prefix_counts_done invariant_in_prefix_counts_cur invariant_in_prefix_no_large)
  exact (goal_5 nums require_1 i_1 cIdx out invariant_rec_out_size out_1 remaining invariant_in_out_size invariant_in_remaining_le invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_in_counts_size invariant_in_cIdx_lt if_pos_1 invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large invariant_in_outPos_le invariant_in_space invariant_in_prefix_sorted invariant_in_prefix_range invariant_in_prefix_counts_done invariant_in_prefix_counts_cur invariant_in_prefix_no_large)
  exact (goal_6 nums require_1 i_1 cIdx out invariant_rec_out_size out_1 remaining invariant_in_out_size invariant_in_remaining_le invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_in_counts_size invariant_in_cIdx_lt if_pos_1 invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large invariant_in_outPos_le invariant_in_space invariant_in_prefix_sorted invariant_in_prefix_range invariant_in_prefix_counts_done invariant_in_prefix_counts_cur invariant_in_prefix_no_large)
  exact (goal_7 nums require_1 i_1 cIdx out invariant_rec_out_size out_1 remaining invariant_in_out_size invariant_in_remaining_le invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_in_counts_size invariant_in_cIdx_lt if_pos_1 invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large invariant_in_outPos_le invariant_in_space invariant_in_prefix_sorted invariant_in_prefix_range invariant_in_prefix_counts_done invariant_in_prefix_counts_cur invariant_in_prefix_no_large)
  exact (goal_8 nums require_1 i_1 cIdx out invariant_rec_out_size invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large)
  exact (goal_9 nums require_1 i_1 cIdx out invariant_rec_out_size invariant_cnt_i_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large)
  exact (goal_10 nums require_1 i_1 cIdx out invariant_rec_out_size i_4 remaining_1 invariant_cnt_i_le invariant_in_out_size invariant_in_remaining_le invariant_rec_counts_size invariant_rec_cIdx_le if_pos invariant_in_counts_size invariant_in_cIdx_lt invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large done_3 invariant_in_outPos_le invariant_in_space invariant_in_prefix_sorted invariant_in_prefix_range invariant_in_prefix_counts_done invariant_in_prefix_counts_cur invariant_in_prefix_no_large)
  exact (goal_11 nums require_1 i_1 i_4 i_5 invariant_cnt_i_le invariant_rec_out_size invariant_rec_counts_size invariant_cnt_size done_1 invariant_cnt_hist invariant_rec_cIdx_le done_2 invariant_rec_outPos_le invariant_rec_prefix_sorted invariant_rec_prefix_range invariant_rec_prefix_counts_done invariant_rec_prefix_no_large)
end Proof
