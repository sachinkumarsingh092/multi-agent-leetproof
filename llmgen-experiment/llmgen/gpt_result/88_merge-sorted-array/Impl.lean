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
    MergeSortedArrays: Merge two sorted integer arrays into a new sorted array.
    Natural language breakdown:
    1. Inputs are two arrays of integers, `nums1` and `nums2`.
    2. Each input array is sorted in non-decreasing order.
    3. The output is a new array whose length is `nums1.size + nums2.size`.
    4. The output is sorted in non-decreasing order.
    5. The output contains exactly the multiset union of elements of `nums1` and `nums2`:
       for every integer value, its number of occurrences in the output equals the sum of its
       occurrences in the two inputs.
    6. Edge cases include empty inputs, singleton inputs, duplicates, and negative values.
    Your algorithm should run in **O(m+n)** time and **O(m+n)** extra space, where m = nums1.size and n = nums2.size.
-/

section Specs
-- Helper predicate: an array is sorted in non-decreasing order.
-- We use adjacent comparisons (local sortedness) for a simple, index-based formulation.
def sortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Helper function: count occurrences of a value in an array.
def countInArray (a : Array Int) (v : Int) : Nat :=
  a.toList.count v

-- Preconditions: both input arrays are sorted in non-decreasing order.
def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  sortedNondecreasing nums1 ∧ sortedNondecreasing nums2

-- Postconditions: result has the correct size, is sorted, and contains exactly all elements.
def postcondition (nums1 : Array Int) (nums2 : Array Int) (result : Array Int) : Prop :=
  result.size = nums1.size + nums2.size ∧
  sortedNondecreasing result ∧
  ∀ v : Int, countInArray result v = countInArray nums1 v + countInArray nums2 v
end Specs

section Impl
method MergeSortedArrays (nums1 : Array Int) (nums2 : Array Int)
  return (result : Array Int)
  require precondition nums1 nums2
  ensures postcondition nums1 nums2 result
  do
  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut k : Nat := 0
  let mut res : Array Int := Array.replicate (nums1.size + nums2.size) (0 : Int)

  while k < res.size
    -- Sizes/bounds to make array indexing safe and relate counters.
    invariant "inv_sizes" (res.size = nums1.size + nums2.size)
    invariant "inv_bounds_k" (k ≤ res.size)
    invariant "inv_bounds_i" (i ≤ nums1.size)
    invariant "inv_bounds_j" (j ≤ nums2.size)
    invariant "inv_k_eq" (k = i + j)
    -- Functional content: the filled prefix is exactly the multiset union of consumed prefixes.
    invariant "inv_counts" (∀ v : Int,
      countInArray (res.extract 0 k) v =
        countInArray (nums1.extract 0 i) v + countInArray (nums2.extract 0 j) v)
    -- Sortedness of the filled prefix.
    invariant "inv_sorted_prefix" (sortedNondecreasing (res.extract 0 k))
    -- Key ordering fact: the last written element is ≤ the next candidate(s).
    invariant "inv_last_le_next" (
      k = 0 ∨
      ((i < nums1.size → res[(k-1)]! ≤ nums1[i]!) ∧
       (j < nums2.size → res[(k-1)]! ≤ nums2[j]!)))
    decreasing (res.size - k)
  do
    -- Prefer flattening: handle exhaustion cases first, then the compare case.
    if i ≥ nums1.size then
      res := res.set! k (nums2[j]!)
      j := j + 1
      k := k + 1
      continue

    if j ≥ nums2.size then
      res := res.set! k (nums1[i]!)
      i := i + 1
      k := k + 1
      continue

    let v1 := nums1[i]!
    let v2 := nums2[j]!
    if v1 ≤ v2 then
      res := res.set! k v1
      i := i + 1
    else
      res := res.set! k v2
      j := j + 1

    k := k + 1

  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- nums1 = [1,2,3], nums2 = [2,5,6] => [1,2,2,3,5,6]
def test1_nums1 : Array Int := #[1, 2, 3]
def test1_nums2 : Array Int := #[2, 5, 6]
def test1_Expected : Array Int := #[1, 2, 2, 3, 5, 6]

-- Test case 2: Example 2
-- nums1 = [1], nums2 = [] => [1]
def test2_nums1 : Array Int := #[1]
def test2_nums2 : Array Int := #[]
def test2_Expected : Array Int := #[1]

-- Test case 3: Example 3
-- nums1 = [], nums2 = [1] => [1]
def test3_nums1 : Array Int := #[]
def test3_nums2 : Array Int := #[1]
def test3_Expected : Array Int := #[1]

-- Test case 4: Both empty
-- [] and [] => []
def test4_nums1 : Array Int := #[]
def test4_nums2 : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: Duplicates across both arrays
-- [1,1,1] and [1,1] => [1,1,1,1,1]
def test5_nums1 : Array Int := #[1, 1, 1]
def test5_nums2 : Array Int := #[1, 1]
def test5_Expected : Array Int := #[1, 1, 1, 1, 1]

-- Test case 6: Negative values and mix
-- [-3,-1,2] and [-2,0,3] => [-3,-2,-1,0,2,3]
def test6_nums1 : Array Int := #[-3, -1, 2]
def test6_nums2 : Array Int := #[-2, 0, 3]
def test6_Expected : Array Int := #[-3, -2, -1, 0, 2, 3]

-- Test case 7: Already separated ranges
-- [1,2,3] and [4,5] => [1,2,3,4,5]
def test7_nums1 : Array Int := #[1, 2, 3]
def test7_nums2 : Array Int := #[4, 5]
def test7_Expected : Array Int := #[1, 2, 3, 4, 5]

-- Test case 8: Interleaving with equal boundary values and many duplicates
-- [0,2,2,2] and [2,2,3] => [0,2,2,2,2,2,3]
def test8_nums1 : Array Int := #[0, 2, 2, 2]
def test8_nums2 : Array Int := #[2, 2, 3]
def test8_Expected : Array Int := #[0, 2, 2, 2, 2, 2, 3]

-- Test case 9: Singleton + singleton with ordering
-- [0] and [1] => [0,1]
def test9_nums1 : Array Int := #[0]
def test9_nums2 : Array Int := #[1]
def test9_Expected : Array Int := #[0, 1]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MergeSortedArrays test1_nums1 test1_nums2).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MergeSortedArrays test2_nums1 test2_nums2).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MergeSortedArrays test3_nums1 test3_nums2).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MergeSortedArrays test4_nums1 test4_nums2).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MergeSortedArrays test5_nums1 test5_nums2).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MergeSortedArrays test6_nums1 test6_nums2).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MergeSortedArrays test7_nums1 test7_nums2).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MergeSortedArrays test8_nums1 test8_nums2).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MergeSortedArrays test9_nums1 test9_nums2).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test MergeSortedArrays (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (invariant_inv_sizes : res.size = nums1.size + nums2.size)
    (invariant_inv_bounds_i : i ≤ nums1.size)
    (invariant_inv_bounds_j : j ≤ nums2.size)
    (invariant_inv_bounds_k : i + j ≤ res.size)
    (if_pos : i + j < res.size)
    (if_pos_1 : nums1.size ≤ i)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!)
    (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!))
    : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums2[j]!)) = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList) := by
    sorry

theorem goal_1
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (invariant_inv_sizes : res.size = nums1.size + nums2.size)
    (invariant_inv_bounds_i : i ≤ nums1.size)
    (invariant_inv_bounds_j : j ≤ nums2.size)
    (invariant_inv_bounds_k : i + j ≤ res.size)
    (if_pos : i + j < res.size)
    (if_pos_1 : nums1.size ≤ i)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!)
    (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!))
    : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
    sorry

theorem goal_2
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (if_pos : i + j < res.size)
    (if_neg : i < nums1.size)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums1[i]!)) = List.count v (List.take (i + OfNat.ofNat 1) nums1.toList) + List.count v (List.take j nums2.toList) := by
  intro v
  classical
  let k : Nat := i + j
  have hkSize : k < res.size := by simpa [k] using if_pos
  have hk : k < res.toList.length := by simpa [Array.length_toList] using hkSize
  have hiL : i < nums1.toList.length := by simpa [Array.length_toList] using if_neg

  have h_arr_get? : nums1[i]? = some nums1[i] := by
    have hi : i < nums1.size := if_neg
    simp [Array.get?, hi]
  have h_list_get? : nums1.toList[i]? = some nums1.toList[i] := by
    simpa using (List.getElem?_eq_getElem (l := nums1.toList) hiL)
  have h_toList_get? : nums1.toList[i]? = nums1[i]? := by
    simpa using (Array.getElem?_toList (xs := nums1) (i := i))
  have h_toList_getElem : nums1.toList[i] = nums1[i] := by
    have hs : some (nums1.toList[i]) = some (nums1[i]) := by
      calc
        some (nums1.toList[i]) = nums1.toList[i]? := by
          simpa [h_list_get?] using (Eq.symm h_list_get?)
        _ = nums1[i]? := by simpa [h_toList_get?]
        _ = some (nums1[i]) := by simpa [h_arr_get?]
    exact Option.some.inj hs

  have h_getBang_eq : nums1[i]! = nums1[i] := by
    have hi : i < nums1.size := if_neg
    simp [Array.get!_eq_getD, Array.getD, Array.get?, hi]
  have h_toList_getBang : nums1.toList[i] = nums1[i]! :=
    h_toList_getElem.trans h_getBang_eq.symm

  have h_take_nums1 : List.take (i + 1) nums1.toList = List.take i nums1.toList ++ [nums1[i]!] := by
    simpa [h_toList_getBang] using
      (List.take_succ_eq_append_getElem (l := nums1.toList) (i := i) hiL)

  have h_take_set_res :
      List.take (k + 1) (res.toList.set k nums1[i]!) = List.take k res.toList ++ [nums1[i]!] := by
    have hkLe : k ≤ res.size := Nat.le_of_lt hkSize
    have hlen : (List.take k res.toList).length = k := by
      simpa [List.length_take, Array.length_toList, Nat.min_eq_left hkLe]
    calc
      List.take (k + 1) (res.toList.set k nums1[i]!)
          = (res.toList.set k nums1[i]!).take (k + 1) := rfl
      _ = (res.toList.take (k + 1)).set k nums1[i]! := by
            simpa using (List.take_set (l := res.toList) (i := k + 1) (j := k) (a := nums1[i]!))
      _ = ((List.take k res.toList ++ [res.toList[k]]).set k nums1[i]!) := by
            simp [List.take_succ_eq_append_getElem (l := res.toList) (i := k) hk]
      _ = List.take k res.toList ++ [nums1[i]!] := by
            simp [List.set_append, hlen]

  have h_count_nums1 :
      List.count v (List.take (i + 1) nums1.toList) =
        List.count v (List.take i nums1.toList) + List.count v [nums1[i]!] := by
    calc
      List.count v (List.take (i + 1) nums1.toList)
          = List.count v (List.take i nums1.toList ++ [nums1[i]!]) := by
              simp [h_take_nums1]
      _ = List.count v (List.take i nums1.toList) + List.count v [nums1[i]!] := by
              simpa using
                (List.count_append (a := v) (l₁ := List.take i nums1.toList) (l₂ := [nums1[i]!]))

  have h_counts :
      List.count v (List.take k res.toList) =
        List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList) := by
    simpa [k] using invariant_inv_counts v

  have h_main :
      List.count v (List.take (k + 1) (res.toList.set k nums1[i]!)) =
        List.count v (List.take (i + 1) nums1.toList) + List.count v (List.take j nums2.toList) := by
    calc
      List.count v (List.take (k + 1) (res.toList.set k nums1[i]!))
          = List.count v (List.take k res.toList ++ [nums1[i]!]) := by
              simp [h_take_set_res]
      _ = List.count v (List.take k res.toList) + List.count v [nums1[i]!] := by
              simpa using
                (List.count_append (a := v) (l₁ := List.take k res.toList) (l₂ := [nums1[i]!]))
      _ = (List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList)) +
            List.count v [nums1[i]!] := by
              simp [h_counts, Nat.add_assoc]
      _ = (List.count v (List.take i nums1.toList) + List.count v [nums1[i]!]) +
            List.count v (List.take j nums2.toList) := by
              ac_rfl
      _ = List.count v (List.take (i + 1) nums1.toList) + List.count v (List.take j nums2.toList) := by
              simp [h_count_nums1]

  simpa [k, Nat.add_assoc] using h_main

theorem goal_3
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (invariant_inv_bounds_i : i ≤ nums1.size)
    (invariant_inv_bounds_j : j ≤ nums2.size)
    (invariant_inv_bounds_k : i + j ≤ res.size)
    (if_pos : i + j < res.size)
    (if_neg : i < nums1.size)
    (if_pos_1 : nums2.size ≤ j)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!)
    (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!))
    : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
  intro i_1 hi1 hi1p
  set k : Nat := i + j
  have hklt : k < res.size := by simpa [k] using if_pos
  have hk_le : k ≤ res.size := Nat.le_of_lt hklt
  have hk1_le : k + 1 ≤ res.size := Nat.succ_le_of_lt hklt

  set res' : Array ℤ := res.setIfInBounds k nums1[i]!
  set pref : Array ℤ := res'.extract 0 (k + 1)

  have hsize_res' : res'.size = res.size := by simp [res']

  have hsize_pref : pref.size = k + 1 := by
    simp [pref, Array.size_extract, hsize_res', Nat.min_eq_left hk1_le]

  have hi1_lt_k : i_1 < k := by simpa [k] using hi1
  have hi1_res : i_1 < res.size := lt_trans (Nat.lt_succ_self i_1) (by simpa using hi1p)

  have hi1_pref : i_1 < pref.size := by
    have : i_1 < k + 1 := Nat.lt_trans hi1_lt_k (Nat.lt_succ_self k)
    simpa [hsize_pref] using this

  have hi1p_pref : i_1 + 1 < pref.size := by
    have : i_1 + 1 < k + 1 := Nat.succ_lt_succ hi1_lt_k
    simpa [hsize_pref] using this

  -- helper: pref[t]! = res'[t]!
  have pref_get_eq_res'_get (t : Nat) (ht : t < pref.size) : pref[t]! = res'[t]! := by
    let ht' : t < res'.size := by
      -- proof produced by extract
      simpa using (by
        have := Array.getElem_extract_aux (xs := res') (start := 0) (stop := k + 1) (i := t) ht
        simpa using this)
    calc
      pref[t]! = pref[t]'ht := by
        simpa using (getElem!_pos pref t ht)
      _ = res'[t]'ht' := by
        -- rewrite via getElem_extract
        have h := (Array.getElem_extract (xs := res') (start := 0) (stop := k + 1) (i := t) (h := ht))
        -- `h` gives `pref[t] = res'[0+t]`, simplify
        simpa [pref] using h
      _ = res'[t]! := by
        simpa using (getElem!_pos res' t ht').symm

  -- helper: res'[t]! = res[t]! if t≠k
  have res'_get_eq_res_get_of_ne (t : Nat) (ht : t < res.size) (hne : k ≠ t) : res'[t]! = res[t]! := by
    have ht' : t < res'.size := by simpa [hsize_res'] using ht
    have htSet : t < (res.setIfInBounds k nums1[i]!).size := by
      simpa [res'] using ht'
    have htSet_expected : t < (res.setIfInBounds k nums1[i]!).size := by
      simpa using ht
    have hpeq : htSet = htSet_expected := by
      apply Subsingleton.elim
    calc
      res'[t]! = res'[t]'ht' := by simpa using (getElem!_pos res' t ht')
      _ = (res.setIfInBounds k nums1[i]!)[t]'htSet := by
        simpa [res']
      _ = (res.setIfInBounds k nums1[i]!)[t]'htSet_expected := by
        cases hpeq; rfl
      _ = res[t]'ht := by
        simpa [hne] using
          (Array.getElem_setIfInBounds_ne (xs := res) (i := k) (a := nums1[i]!) (j := t) ht hne)
      _ = res[t]! := by simpa using (getElem!_pos res t ht).symm

  -- helper: (res.extract 0 k)[t]! = res[t]!
  have oldpref_get_eq_res_get (t : Nat) (ht : t < k) : (res.extract 0 k)[t]! = res[t]! := by
    have hsize_old : (res.extract 0 k).size = k := by
      simp [Array.size_extract, Nat.min_eq_left hk_le]
    have ht_old : t < (res.extract 0 k).size := by simpa [hsize_old] using ht
    let ht' : t < res.size := by
      have := Array.getElem_extract_aux (xs := res) (start := 0) (stop := k) (i := t) ht_old
      simpa using this
    calc
      (res.extract 0 k)[t]! = (res.extract 0 k)[t]'ht_old := by
        simpa using (getElem!_pos (res.extract 0 k) t ht_old)
      _ = res[t]'ht' := by
        have h := (Array.getElem_extract (xs := res) (start := 0) (stop := k) (i := t) (h := ht_old))
        simpa using h
      _ = res[t]! := by
        simpa using (getElem!_pos res t ht').symm

  have hi1p_le_k : i_1 + 1 ≤ k := Nat.succ_le_of_lt hi1_lt_k
  rcases lt_or_eq_of_le hi1p_le_k with hlt | heq
  · -- case: i_1+1 < k
    have hi1p_lt_k : i_1 + 1 < k := hlt

    have h_pref_i1 : pref[i_1]! = res[i_1]! := by
      calc
        pref[i_1]! = res'[i_1]! := pref_get_eq_res'_get i_1 hi1_pref
        _ = res[i_1]! :=
          res'_get_eq_res_get_of_ne i_1 hi1_res (Nat.ne_of_gt hi1_lt_k)

    have h_pref_i1p : pref[i_1 + 1]! = res[i_1 + 1]! := by
      have hi1p_res : i_1 + 1 < res.size := by simpa using hi1p
      calc
        pref[i_1 + 1]! = res'[i_1 + 1]! := pref_get_eq_res'_get (i_1 + 1) hi1p_pref
        _ = res[i_1 + 1]! :=
          res'_get_eq_res_get_of_ne (i_1 + 1) hi1p_res (Nat.ne_of_gt hi1p_lt_k)

    have hold : res[i_1]! ≤ res[i_1 + 1]! := by
      have hs :=
        invariant_inv_sorted_prefix i_1 (by simpa [k] using hi1p_lt_k) (by simpa using hi1p)
      have hx1 : (res.extract 0 k)[i_1]! = res[i_1]! := oldpref_get_eq_res_get i_1 hi1_lt_k
      have hx2 : (res.extract 0 k)[i_1 + 1]! = res[i_1 + 1]! :=
        oldpref_get_eq_res_get (i_1 + 1) hi1p_lt_k
      simpa [hx1, hx2] using hs

    simpa [h_pref_i1, h_pref_i1p] using hold

  · -- case: i_1+1 = k
    have hk_pref : k < pref.size := by
      have : k < k + 1 := Nat.lt_succ_self k
      simpa [hsize_pref] using this

    have hi1_eq : i_1 = k - 1 := by
      have h' := congrArg (fun n => n - 1) heq
      simpa using h'

    have h_pref_i1 : pref[i_1]! = res[k - 1]! := by
      calc
        pref[i_1]! = res'[i_1]! := pref_get_eq_res'_get i_1 hi1_pref
        _ = res[i_1]! :=
          res'_get_eq_res_get_of_ne i_1 hi1_res (Nat.ne_of_gt hi1_lt_k)
        _ = res[k - 1]! := by simpa [hi1_eq]

    -- res'[k]! is the newly written value
    have h_res'k : res'[k]! = nums1[i]! := by
      have hk' : k < res'.size := by simpa [hsize_res'] using hklt
      have hkSet : k < (res.setIfInBounds k nums1[i]!).size := by
        simpa [res'] using hk'
      have hkSet_expected : k < (res.setIfInBounds k nums1[i]!).size := by
        simpa using hklt
      have hpeq : hkSet = hkSet_expected := by
        apply Subsingleton.elim
      calc
        res'[k]! = res'[k]'hk' := by
          simpa using (getElem!_pos res' k hk')
        _ = (res.setIfInBounds k nums1[i]!)[k]'hkSet := by
          simpa [res']
        _ = (res.setIfInBounds k nums1[i]!)[k]'hkSet_expected := by
          cases hpeq; rfl
        _ = nums1[i]! := by
          simpa using
            (by
              simpa using
                (Array.getElem_setIfInBounds (xs := res) (i := k) (a := nums1[i]!) (j := k) hklt))

    have h_pref_i1p : pref[i_1 + 1]! = nums1[i]! := by
      calc
        pref[i_1 + 1]! = pref[k]! := by simpa [heq]
        _ = res'[k]! := pref_get_eq_res'_get k hk_pref
        _ = nums1[i]! := h_res'k

    have h_boundary : res[k - 1]! ≤ nums1[i]! := by
      cases invariant_inv_last_le_next with
      | inl h00 =>
        rcases h00 with ⟨hi0, hj0⟩
        subst hi0; subst hj0
        simp [k] at hi1_lt_k
      | inr hnext =>
        have := hnext.1 if_neg
        simpa [k] using this

    simpa [h_pref_i1, h_pref_i1p] using h_boundary

theorem goal_4
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (if_pos : i + j < res.size)
    (if_neg : i < nums1.size)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums1[i]!)) = List.count v (List.take (i + OfNat.ofNat 1) nums1.toList) + List.count v (List.take j nums2.toList) := by
    intros; expose_names; exact goal_2 nums1 nums2 i j res if_pos if_neg invariant_inv_counts v



theorem goal_5
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (invariant_inv_sizes : res.size = nums1.size + nums2.size)
    (invariant_inv_bounds_i : i ≤ nums1.size)
    (invariant_inv_bounds_j : j ≤ nums2.size)
    (if_pos_1 : nums1[i]! ≤ nums2[j]!)
    (invariant_inv_bounds_k : i + j ≤ res.size)
    (if_pos : i + j < res.size)
    (if_neg : i < nums1.size)
    (if_neg_1 : j < nums2.size)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!)
    (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!))
    : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums1[i]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
    sorry

theorem goal_6
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (invariant_inv_sizes : res.size = nums1.size + nums2.size)
    (invariant_inv_bounds_i : i ≤ nums1.size)
    (invariant_inv_bounds_j : j ≤ nums2.size)
    (invariant_inv_bounds_k : i + j ≤ res.size)
    (if_pos : i + j < res.size)
    (if_neg : i < nums1.size)
    (if_neg_1 : j < nums2.size)
    (if_neg_2 : nums2[j]! < nums1[i]!)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!)
    (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!))
    : ∀ (v : ℤ), List.count v (List.take (i + j + OfNat.ofNat 1) (res.toList.set (i + j) nums2[j]!)) = List.count v (List.take i nums1.toList) + List.count v (List.take (j + OfNat.ofNat 1) nums2.toList) := by
    sorry

theorem goal_7
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (j : ℕ)
    (res : Array ℤ)
    (invariant_inv_sizes : res.size = nums1.size + nums2.size)
    (invariant_inv_bounds_i : i ≤ nums1.size)
    (invariant_inv_bounds_j : j ≤ nums2.size)
    (invariant_inv_bounds_k : i + j ≤ res.size)
    (if_pos : i + j < res.size)
    (if_neg : i < nums1.size)
    (if_neg_1 : j < nums2.size)
    (if_neg_2 : nums2[j]! < nums1[i]!)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i + j) res.toList) = List.count v (List.take i nums1.toList) + List.count v (List.take j nums2.toList))
    (invariant_inv_sorted_prefix : ∀ (i_1 : ℕ), i_1 + OfNat.ofNat 1 < i + j → i_1 + OfNat.ofNat 1 < res.size → (res.extract (OfNat.ofNat 0) (i + j))[i_1]! ≤ (res.extract (OfNat.ofNat 0) (i + j))[i_1 + OfNat.ofNat 1]!)
    (invariant_inv_last_le_next : i = OfNat.ofNat 0 ∧ j = OfNat.ofNat 0 ∨ (i < nums1.size → res[i + j - OfNat.ofNat 1]! ≤ nums1[i]!) ∧ (j < nums2.size → res[i + j - OfNat.ofNat 1]! ≤ nums2[j]!))
    : ∀ i_1 < i + j, i_1 + OfNat.ofNat 1 < res.size → ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1]! ≤ ((res.setIfInBounds (i + j) nums2[j]!).extract (OfNat.ofNat 0) (i + j + OfNat.ofNat 1))[i_1 + OfNat.ofNat 1]! := by
    sorry

theorem goal_8
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (require_1 : (∀ (i : ℕ), i + OfNat.ofNat 1 < nums1.size → nums1[i]! ≤ nums1[i + OfNat.ofNat 1]!) ∧ ∀ (i : ℕ), i + OfNat.ofNat 1 < nums2.size → nums2[i]! ≤ nums2[i + OfNat.ofNat 1]!)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (res_1 : Array ℤ)
    (invariant_inv_bounds_i : i_1 ≤ nums1.size)
    (invariant_inv_bounds_j : i_2 ≤ nums2.size)
    (invariant_inv_sizes : res_1.size = nums1.size + nums2.size)
    (invariant_inv_bounds_k : i_1 + i_2 ≤ res_1.size)
    (invariant_inv_sorted_prefix : ∀ (i : ℕ), i + OfNat.ofNat 1 < i_1 + i_2 → i + OfNat.ofNat 1 < res_1.size → (res_1.extract (OfNat.ofNat 0) (i_1 + i_2))[i]! ≤ (res_1.extract (OfNat.ofNat 0) (i_1 + i_2))[i + OfNat.ofNat 1]!)
    (done_1 : res_1.size ≤ i_1 + i_2)
    (invariant_inv_counts : ∀ (v : ℤ), List.count v (List.take (i_1 + i_2) res_1.toList) = List.count v (List.take i_1 nums1.toList) + List.count v (List.take i_2 nums2.toList))
    (invariant_inv_last_le_next : i_1 = OfNat.ofNat 0 ∧ i_2 = OfNat.ofNat 0 ∨ (i_1 < nums1.size → res_1[i_1 + i_2 - OfNat.ofNat 1]! ≤ nums1[i_1]!) ∧ (i_2 < nums2.size → res_1[i_1 + i_2 - OfNat.ofNat 1]! ≤ nums2[i_2]!))
    : postcondition nums1 nums2 res_1 := by
    sorry



prove_correct MergeSortedArrays by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums1 nums2 require_1 i j res invariant_inv_sizes invariant_inv_bounds_i invariant_inv_bounds_j invariant_inv_bounds_k if_pos if_pos_1 invariant_inv_counts invariant_inv_sorted_prefix invariant_inv_last_le_next)
  exact (goal_1 nums1 nums2 require_1 i j res invariant_inv_sizes invariant_inv_bounds_i invariant_inv_bounds_j invariant_inv_bounds_k if_pos if_pos_1 invariant_inv_counts invariant_inv_sorted_prefix invariant_inv_last_le_next)
  exact (goal_2 nums1 nums2 i j res if_pos if_neg invariant_inv_counts)
  exact (goal_3 nums1 nums2 i j res invariant_inv_bounds_i invariant_inv_bounds_j invariant_inv_bounds_k if_pos if_neg if_pos_1 invariant_inv_counts invariant_inv_sorted_prefix invariant_inv_last_le_next)
  exact (goal_4 nums1 nums2 i j res if_pos if_neg invariant_inv_counts)
  exact (goal_5 nums1 nums2 require_1 i j res invariant_inv_sizes invariant_inv_bounds_i invariant_inv_bounds_j if_pos_1 invariant_inv_bounds_k if_pos if_neg if_neg_1 invariant_inv_counts invariant_inv_sorted_prefix invariant_inv_last_le_next)
  exact (goal_6 nums1 nums2 require_1 i j res invariant_inv_sizes invariant_inv_bounds_i invariant_inv_bounds_j invariant_inv_bounds_k if_pos if_neg if_neg_1 if_neg_2 invariant_inv_counts invariant_inv_sorted_prefix invariant_inv_last_le_next)
  exact (goal_7 nums1 nums2 require_1 i j res invariant_inv_sizes invariant_inv_bounds_i invariant_inv_bounds_j invariant_inv_bounds_k if_pos if_neg if_neg_1 if_neg_2 invariant_inv_counts invariant_inv_sorted_prefix invariant_inv_last_le_next)
  exact (goal_8 nums1 nums2 require_1 i_1 i_2 res_1 invariant_inv_bounds_i invariant_inv_bounds_j invariant_inv_sizes invariant_inv_bounds_k invariant_inv_sorted_prefix done_1 invariant_inv_counts invariant_inv_last_le_next)
end Proof
