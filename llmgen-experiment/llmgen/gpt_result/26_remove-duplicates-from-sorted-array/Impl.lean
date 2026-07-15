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
    RemoveDuplicatesFromSortedArray: Remove duplicates from a sorted integer array in-place and return the number of unique elements.
    Natural language breakdown:
    1. The input is an array of integers `nums` that is sorted in non-decreasing order.
    2. We return a natural number `k` that equals the number of distinct values appearing in `nums`.
    3. We also return an output array `out` of the same size as `nums`.
    4. The first `k` elements of `out` contain each distinct value from `nums` exactly once.
    5. These first `k` elements are in the same order as they appear in `nums` (stability).
    6. Since `nums` is sorted, the `out` prefix of length `k` is strictly increasing.
    7. Elements of `out` at indices ≥ k are unspecified and can be ignored.
    8. Edge cases: empty array (k = 0), singleton (k = 1), all equal (k = 1), already strictly increasing (k = nums.size).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: sorted (non-decreasing) predicate on arrays, phrased with Nat indices.
def ArraySortedLe (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

-- Helper: prefix is strictly increasing (hence no duplicates in the prefix).
def PrefixStrictIncreasing (a : Array Int) (k : Nat) : Prop :=
  k ≤ a.size ∧ ∀ (i : Nat), i + 1 < k → a[i]! < a[i + 1]!

-- Helper: membership agreement between input and the produced unique prefix.
-- Every value appearing anywhere in nums appears in the first k cells of out, and vice-versa.
def PrefixSameMembers (nums : Array Int) (k : Nat) (out : Array Int) : Prop :=
  k ≤ out.size ∧
    ∀ (x : Int), x ∈ nums ↔ (∃ (i : Nat), i < k ∧ out[i]! = x)

-- Helper: stability/order. There exists a strictly increasing index map f selecting the prefix
-- elements from nums in order. Additionally, each selected index is the first occurrence of that value.
def PrefixOccursInOrderFirst (nums : Array Int) (out : Array Int) (k : Nat) : Prop :=
  ∃ (f : Nat → Nat),
    (∀ (i : Nat), i < k → f i < nums.size ∧ out[i]! = nums[f i]!) ∧
    (∀ (i : Nat) (j : Nat), i < j → j < k → f i < f j) ∧
    (∀ (i : Nat), i < k → ∀ (j : Nat), j < f i → nums[j]! ≠ out[i]!)

-- Precondition: input is sorted in non-decreasing order.
def precondition (nums : Array Int) : Prop :=
  ArraySortedLe nums

-- Postcondition: result k is the number of unique elements; out is same size as nums;
-- first k positions are unique values in stable order; rest is irrelevant.
def postcondition (nums : Array Int) (result : Nat) (out : Array Int) : Prop :=
  out.size = nums.size ∧
    PrefixStrictIncreasing out result ∧
    PrefixSameMembers nums result out ∧
    PrefixOccursInOrderFirst nums out result
end Specs

section Impl
method RemoveDuplicatesFromSortedArray (nums : Array Int)
  return (res : Nat × Array Int)
  require precondition nums
  ensures postcondition nums res.1 res.2
  do
    let n := nums.size
    if n = 0 then
      return (0, nums)
    else
      -- out will hold the unique prefix; we keep size = n (O(1) extra space besides output array).
      let mut out := Array.replicate n (0 : Int)
      -- write index for the unique prefix
      let mut k : Nat := 1
      -- first element is always kept
      out := out.set! 0 (nums[0]!)

      let mut i : Nat := 1
      while i < n
        -- out stays the same size as the input buffer size n.
        invariant "inv_out_size" out.size = n
        -- indices are in range; k counts uniques seen in nums[0..i).
        invariant "inv_bounds" (1 ≤ k ∧ k ≤ i ∧ i ≤ n)
        -- the first element is preserved in the output prefix.
        invariant "inv_first" out[0]! = nums[0]!
        -- the last written unique equals the last element in the processed prefix.
        invariant "inv_last" out[k - 1]! = nums[i - 1]!
        -- the written prefix contains no duplicates (strictly increasing => unique).
        invariant "inv_strict" (∀ (j : Nat), j + 1 < k → out[j]! < out[j + 1]!)
        -- membership in processed prefix nums[0..i) matches membership in out[0..k).
        invariant "inv_members_prefix" (∀ (x : Int), (∃ (t : Nat), t < i ∧ nums[t]! = x) ↔ (∃ (j : Nat), j < k ∧ out[j]! = x))
        decreasing n - i
      do
        let cur := nums[i]!
        let prev := nums[i - 1]!
        if cur = prev then
          i := i + 1
          continue
        else
          out := out.set! k cur
          k := k + 1
          i := i + 1

      return (k, out)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: nums = [1,1,2]
-- Output: k = 2, prefix = [1,2]
def test1_nums : Array Int := #[1, 1, 2]
def test1_Expected : Nat × Array Int := (2, #[1, 2, 0])

-- Test case 2: Example 2
-- Input: nums = [0,0,1,1,1,2,2,3,3,4]
-- Output: k = 5, prefix = [0,1,2,3,4]
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
def test2_Expected : Nat × Array Int := (5, #[0, 1, 2, 3, 4, 0, 0, 0, 0, 0])

-- Test case 3: Empty array
-- Output: k = 0, out empty
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])

-- Test case 4: Singleton array
-- Output: k = 1, prefix = [7]
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])

-- Test case 5: All equal elements
-- Output: k = 1, prefix = [2]
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (1, #[2, 0, 0, 0])

-- Test case 6: Already strictly increasing
-- Output: k = size, out may equal input
def test6_nums : Array Int := #[1, 2, 3, 4]
def test6_Expected : Nat × Array Int := (4, #[1, 2, 3, 4])

-- Test case 7: Includes negative values and duplicates
-- Input: [-3,-3,-1,-1,0,2,2] -> uniques [-3,-1,0,2]
def test7_nums : Array Int := #[-3, -3, -1, -1, 0, 2, 2]
def test7_Expected : Nat × Array Int := (4, #[-3, -1, 0, 2, 0, 0, 0])

-- Test case 8: Duplicates at the beginning only
-- Input: [0,0,0,1,2,3] -> uniques [0,1,2,3]
def test8_nums : Array Int := #[0, 0, 0, 1, 2, 3]
def test8_Expected : Nat × Array Int := (4, #[0, 1, 2, 3, 0, 0])

-- Test case 9: Duplicates at the end only
-- Input: [1,2,3,4,4,4] -> uniques [1,2,3,4]
def test9_nums : Array Int := #[1, 2, 3, 4, 4, 4]
def test9_Expected : Nat × Array Int := (4, #[1, 2, 3, 4, 0, 0])

-- Recommend to validate: precondition, postcondition, RemoveDuplicatesFromSortedArray
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArray test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test RemoveDuplicatesFromSortedArray (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (a : OfNat.ofNat 1 ≤ k)
    (a_1 : k ≤ i)
    (invariant_inv_members_prefix : ∀ (x : ℤ), (∃ t < i, nums[t]! = x) ↔ ∃ j < k, out[j]! = x)
    (if_pos_1 : nums[i]! = nums[i - OfNat.ofNat 1]!)
    : ∀ (x : ℤ), (∃ t < i + OfNat.ofNat 1, nums[t]! = x) ↔ ∃ j < k, out[j]! = x := by
  intro x
  have hi1 : (1 : Nat) ≤ i := le_trans a a_1
  have hi_ne0 : i ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi1)

  have hbridge : (∃ t < i + 1, nums[t]! = x) ↔ (∃ t < i, nums[t]! = x) := by
    constructor
    · rintro ⟨t, ht, htx⟩
      have ht_le : t ≤ i := Nat.lt_succ_iff.mp (by simpa using ht)
      rcases (lt_or_eq_of_le ht_le) with ht_lt | ht_eq
      · exact ⟨t, ht_lt, htx⟩
      · -- t = i
        subst t
        have hi_sub_lt : i - 1 < i := Nat.sub_one_lt hi_ne0
        have hx' : nums[i - 1]! = x := by
          calc
            nums[i - 1]! = nums[i]! := by
              simpa using if_pos_1.symm
            _ = x := htx
        exact ⟨i - 1, hi_sub_lt, hx'⟩
    · rintro ⟨t, ht, htx⟩
      exact ⟨t, Nat.lt_succ_of_lt ht, htx⟩

  -- chain with the existing invariant
  -- (note: goal uses i + OfNat.ofNat 1, which is definitionaly i + 1)
  simpa using (hbridge.trans (invariant_inv_members_prefix x))

theorem goal_1
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_out_size : out.size = nums.size)
    (a : OfNat.ofNat 1 ≤ k)
    (a_1 : k ≤ i)
    (invariant_inv_last : out[k - OfNat.ofNat 1]! = nums[i - OfNat.ofNat 1]!)
    (invariant_inv_strict : ∀ (j : ℕ), j + OfNat.ofNat 1 < k → out[j]! < out[j + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    (if_neg_1 : ¬nums[i]! = nums[i - OfNat.ofNat 1]!)
    : ∀ (j : ℕ), j + OfNat.ofNat 1 < k + OfNat.ofNat 1 → (out.set! k nums[i]!)[j]! < (out.set! k nums[i]!)[j + OfNat.ofNat 1]! := by
  classical

  -- helper: readback after setIfInBounds at a different index
  have hset_ne (xs : Array ℤ) (i j : Nat) (v : ℤ) (h : i ≠ j) :
      (xs.setIfInBounds i v)[j]! = xs[j]! := by
    rw [← Array.get!Internal_eq_getElem! (a := xs.setIfInBounds i v) (i := j)]
    rw [← Array.get!Internal_eq_getElem! (a := xs) (i := j)]
    have hop : (xs.setIfInBounds i v)[j]? = xs[j]? := by
      simpa using
        (Array.getElem?_setIfInBounds_ne (xs := xs) (i := i) (j := j) h (a := v))
    simp [Array.get!Internal, hop]

  -- helper: readback after setIfInBounds at the updated index, assuming in-bounds
  have hset_self (xs : Array ℤ) (i : Nat) (v : ℤ) (hi : i < xs.size) :
      (xs.setIfInBounds i v)[i]! = v := by
    rw [← Array.get!Internal_eq_getElem! (a := xs.setIfInBounds i v) (i := i)]
    simp [Array.get!Internal, Array.getElem?_setIfInBounds_self, hi]

  intro j hj

  have hj' : j + 1 < k + 1 := by simpa using hj
  have hjlt : j < k := (Nat.add_one_lt_add_one_iff).1 hj'
  have hj1le : j + 1 ≤ k := (Nat.lt_iff_add_one_le).1 hjlt

  cases lt_or_eq_of_le hj1le with
  | inl hlt =>
      -- j+1 < k
      have hjne : k ≠ j := ne_of_gt (Nat.lt_of_succ_lt hlt)
      have hj1ne : k ≠ j + 1 := ne_of_gt hlt

      have hreadj : (out.setIfInBounds k nums[i]!)[j]! = out[j]! :=
        hset_ne out k j (nums[i]!) hjne
      have hreadj1 : (out.setIfInBounds k nums[i]!)[j + 1]! = out[j + 1]! :=
        hset_ne out k (j + 1) (nums[i]!) hj1ne

      have hstrict : out[j]! < out[j + 1]! := by
        simpa using (invariant_inv_strict j (by simpa using hlt))

      have : (out.setIfInBounds k nums[i]!)[j]! < (out.setIfInBounds k nums[i]!)[j + 1]! := by
        calc
          (out.setIfInBounds k nums[i]!)[j]! = out[j]! := hreadj
          _ < out[j + 1]! := hstrict
          _ = (out.setIfInBounds k nums[i]!)[j + 1]! := by
            simpa using hreadj1.symm

      -- back to set!
      simpa [Array.set!] using this

  | inr heq =>
      -- j+1 = k, so j = k-1
      have hklt_nums : k < nums.size := lt_of_le_of_lt a_1 if_pos
      have hklt_out : k < out.size := by simpa [invariant_inv_out_size] using hklt_nums
      have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel a
      have hjk1 : j = k - 1 := by
        have : j + 1 = k - 1 + 1 := by simpa [hkpred] using heq
        exact Nat.add_right_cancel this
      subst hjk1

      have hk1lt : k - 1 < k := by
        simpa [Nat.succ_eq_add_one, hkpred] using (Nat.lt_succ_self (k - 1))
      have hk1ne : k ≠ k - 1 := ne_of_gt hk1lt

      have hleft : (out.setIfInBounds k nums[i]!)[k - 1]! = out[k - 1]! :=
        hset_ne out k (k - 1) (nums[i]!) hk1ne
      have hright : (out.setIfInBounds k nums[i]!)[k]! = nums[i]! :=
        hset_self out k (nums[i]!) hklt_out

      have hs : ArraySortedLe nums := require_1
      have hi1 : 1 ≤ i := le_trans a a_1
      have hbound : i - 1 + 1 < nums.size := by
        simpa [Nat.sub_add_cancel hi1] using if_pos
      have hle : nums[i - 1]! ≤ nums[i]! := by
        simpa [Nat.sub_add_cancel hi1] using (hs (i - 1) hbound)
      have hne : nums[i - 1]! ≠ nums[i]! := by
        simpa [eq_comm] using if_neg_1
      have hlt : nums[i - 1]! < nums[i]! := lt_of_le_of_ne hle hne

      have : (out.setIfInBounds k nums[i]!)[k - 1]! < (out.setIfInBounds k nums[i]!)[k]! := by
        calc
          (out.setIfInBounds k nums[i]!)[k - 1]! = out[k - 1]! := hleft
          _ = nums[i - 1]! := by simpa using invariant_inv_last
          _ < nums[i]! := hlt
          _ = (out.setIfInBounds k nums[i]!)[k]! := by
            symm
            exact hright

      simpa [Array.set!, hkpred] using this

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_out_size : out.size = nums.size)
    (a_1 : k ≤ i)
    (invariant_inv_members_prefix : ∀ (x : ℤ), (∃ t < i, nums[t]! = x) ↔ ∃ j < k, out[j]! = x)
    (if_pos : i < nums.size)
    : ∀ (x : ℤ), (∃ t < i + OfNat.ofNat 1, nums[t]! = x) ↔ ∃ j < k + OfNat.ofNat 1, (out.set! k nums[i]!)[j]! = x := by
  intro x

  have hk_nums : k < nums.size := lt_of_le_of_lt a_1 if_pos
  have hk_out : k < out.size := by
    simpa [invariant_inv_out_size] using hk_nums

  have hmem : (∃ t < i, nums[t]! = x) ↔ ∃ j < k, out[j]! = x := by
    simpa using invariant_inv_members_prefix x

  have hget_set_ne (j : Nat) (hne : k ≠ j) : (out.set! k nums[i]!)[j]! = out[j]! := by
    change (out.set! k nums[i]!).get! j = out.get! j
    simp [Array.get!_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hne]

  have hget_set_self : (out.set! k nums[i]!)[k]! = nums[i]! := by
    change (out.set! k nums[i]!).get! k = nums.get! i
    -- compute the LHS via setIfInBounds; close the remaining RHS by unfolding get!
    simp [Array.get!_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, hk_out]
    -- goal may reduce to the standard characterization of get!
    simpa using (Array.get!_eq_getD_getElem? nums i)

  constructor
  · rintro ⟨t, ht, htx⟩
    have ht_le : t ≤ i :=
      (Nat.lt_succ_iff).1 (by simpa [Nat.succ_eq_add_one] using ht)
    cases Nat.eq_or_lt_of_le ht_le with
    | inl hEq =>
        -- t = i
        have hx : nums[i]! = x := by simpa [hEq] using htx
        refine ⟨k, Nat.lt_succ_self k, ?_⟩
        -- value at k is the newly written one
        calc
          (out.set! k nums[i]!)[k]! = nums[i]! := hget_set_self
          _ = x := hx
    | inr hLt =>
        -- t < i, use membership invariant
        rcases (hmem.mp ⟨t, hLt, htx⟩) with ⟨j, hjk, hjx⟩
        refine ⟨j, Nat.lt_trans hjk (Nat.lt_succ_self k), ?_⟩
        have hne : k ≠ j := (Nat.ne_of_lt hjk).symm
        calc
          (out.set! k nums[i]!)[j]! = out[j]! := hget_set_ne j hne
          _ = x := hjx

  · rintro ⟨j, hjlt, hjx⟩
    have hjle : j ≤ k :=
      (Nat.lt_succ_iff).1 (by simpa [Nat.succ_eq_add_one] using hjlt)
    cases Nat.eq_or_lt_of_le hjle with
    | inl hEq =>
        -- j = k
        have this : (out.set! k nums[i]!)[k]! = x := by simpa [hEq] using hjx
        have hx : nums[i]! = x := Eq.trans (Eq.symm hget_set_self) this
        refine ⟨i, ?_, hx⟩
        simpa using (Nat.lt_succ_self i)
    | inr hLt =>
        -- j < k
        have hne : k ≠ j := (Nat.ne_of_lt hLt).symm
        have hjx_out : out[j]! = x := by
          -- update doesn't affect index j
          exact (Eq.trans (Eq.symm (hget_set_ne j hne)) hjx)
        rcases (hmem.mpr ⟨j, hLt, hjx_out⟩) with ⟨t, ht, htx⟩
        refine ⟨t, Nat.lt_trans ht (Nat.lt_succ_self i), htx⟩

theorem goal_3
    (nums : Array ℤ)
    (require_1 : precondition nums)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (out_1 : Array ℤ)
    (a_2 : i_1 ≤ nums.size)
    (done_1 : ¬i_1 < nums.size)
    (a : OfNat.ofNat 1 ≤ i_2)
    (a_1 : i_2 ≤ i_1)
    (invariant_inv_out_size : out_1.size = nums.size)
    (invariant_inv_strict : ∀ (j : ℕ), j + OfNat.ofNat 1 < i_2 → out_1[j]! < out_1[j + OfNat.ofNat 1]!)
    (invariant_inv_members_prefix : ∀ (x : ℤ), (∃ t < i_1, nums[t]! = x) ↔ ∃ j < i_2, out_1[j]! = x)
    : postcondition nums i_2 out_1 := by
    classical

    have hi1 : i_1 = nums.size := by
      apply Nat.le_antisymm a_2
      exact Nat.le_of_not_lt done_1

    have hi2_le_nums : i_2 ≤ nums.size := by
      simpa [hi1] using a_1

    have hi2_le_out : i_2 ≤ out_1.size := by
      simpa [invariant_inv_out_size] using hi2_le_nums

    -- A small helper: in-bounds get! agrees with getElem.
    have getBang_eq_getElem {xs : Array ℤ} {i : Nat} (hi : i < xs.size) : xs[i]! = xs[i]'hi := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hi]

    -- membership ↔ exists index with get!
    have mem_iff_exists_getBang (xs : Array ℤ) (x : ℤ) :
        x ∈ xs ↔ ∃ t : Nat, t < xs.size ∧ xs[t]! = x := by
      constructor
      · intro hx
        rcases (Array.mem_iff_getElem.mp hx) with ⟨t, ht, htx⟩
        refine ⟨t, ht, ?_⟩
        calc
          xs[t]! = xs[t]'ht := by simpa using (getBang_eq_getElem (xs := xs) ht)
          _ = x := htx
      · rintro ⟨t, ht, htx⟩
        refine Array.mem_iff_getElem.mpr ?_
        refine ⟨t, ht, ?_⟩
        calc
          xs[t]'ht = xs[t]! := by
            symm
            simpa using (getBang_eq_getElem (xs := xs) ht)
          _ = x := htx

    -- monotonicity of a sorted array (adjacent ≤) for arbitrary indices.
    have nums_mono : ∀ {p q : Nat}, p < q → q < nums.size → nums[p]! ≤ nums[q]! := by
      intro p q hpq hq
      rcases Nat.exists_eq_add_of_lt hpq with ⟨n, rfl⟩
      -- it suffices to show: for any n, if p+n+1 < size, then nums[p] ≤ nums[p+n+1]
      have haux : ∀ n : Nat, p + n + 1 < nums.size → nums[p]! ≤ nums[p + n + 1]! := by
        intro n
        induction n with
        | zero =>
            intro hn
            -- p+1 < size
            simpa [Nat.add_assoc, Nat.zero_add] using (require_1 p (by simpa [Nat.add_assoc, Nat.zero_add] using hn))
        | succ n ih =>
            intro hn
            have hn' : p + n + 1 < nums.size := by
              omega
            have hmid : nums[p]! ≤ nums[p + n + 1]! := ih hn'
            have hstep : nums[p + n + 1]! ≤ nums[p + n + 2]! := by
              have : p + n + 1 + 1 < nums.size := by
                -- this is exactly hn, simplified
                simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (require_1 (p + n + 1) this)
            exact le_trans hmid hstep
      -- apply the auxiliary lemma
      exact haux n hq

    -- strict monotonicity of the produced prefix for arbitrary indices < i_2.
    have out_strict_mono : ∀ {p q : Nat}, p < q → q < i_2 → out_1[p]! < out_1[q]! := by
      intro p q hpq hq
      rcases Nat.exists_eq_add_of_lt hpq with ⟨n, rfl⟩
      have haux : ∀ n : Nat, p + n + 1 < i_2 → out_1[p]! < out_1[p + n + 1]! := by
        intro n
        induction n with
        | zero =>
            intro hn
            simpa [Nat.add_assoc, Nat.zero_add] using (invariant_inv_strict p (by simpa [Nat.add_assoc, Nat.zero_add] using hn))
        | succ n ih =>
            intro hn
            have hn' : p + n + 1 < i_2 := by
              omega
            have hmid : out_1[p]! < out_1[p + n + 1]! := ih hn'
            have hstep : out_1[p + n + 1]! < out_1[p + n + 2]! := by
              have : p + n + 1 + 1 < i_2 := by
                simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (invariant_inv_strict (p + n + 1) this)
            exact lt_trans hmid hstep
      exact haux n hq

    -- existence of an occurrence in nums for each output prefix element
    have hexists (i : Nat) (hi : i < i_2) : ∃ t : Nat, t < nums.size ∧ nums[t]! = out_1[i]! := by
      have : ∃ j < i_2, out_1[j]! = out_1[i]! := ⟨i, hi, rfl⟩
      have hleft : ∃ t < i_1, nums[t]! = out_1[i]! :=
        (invariant_inv_members_prefix (out_1[i]!)).2 this
      rcases hleft with ⟨t, ht, hEq⟩
      refine ⟨t, ?_, hEq⟩
      simpa [hi1] using ht

    -- Build the index-selection function picking the first occurrence.
    let f : Nat → Nat := fun i =>
      if hi : i < i_2 then
        Nat.find (hexists i hi)
      else
        0

    have hf_spec : ∀ (i : Nat), i < i_2 → f i < nums.size ∧ out_1[i]! = nums[f i]! := by
      intro i hi
      have hfind : (Nat.find (hexists i hi)) < nums.size ∧ nums[Nat.find (hexists i hi)]! = out_1[i]! :=
        Nat.find_spec (hexists i hi)
      have hf : f i = Nat.find (hexists i hi) := by
        simp [f, hi]
      refine ⟨?_, ?_⟩
      · simpa [hf] using hfind.1
      · have : nums[f i]! = out_1[i]! := by
          simpa [hf] using hfind.2
        simpa [this] using this.symm

    refine And.intro invariant_inv_out_size ?_
    refine And.intro ?_ (And.intro ?_ ?_)

    · -- PrefixStrictIncreasing
      refine And.intro hi2_le_out ?_
      intro j hj
      simpa using invariant_inv_strict j hj

    · -- PrefixSameMembers
      refine And.intro hi2_le_out ?_
      intro x
      have hmem : x ∈ nums ↔ ∃ t < i_1, nums[t]! = x := by
        simpa [hi1] using (mem_iff_exists_getBang nums x)
      simpa [hmem] using (invariant_inv_members_prefix x)

    · -- PrefixOccursInOrderFirst
      refine ⟨f, ?_, ?_, ?_⟩
      · intro i hi
        have h := hf_spec i hi
        exact ⟨h.1, h.2⟩
      · intro i j hij hj
        have hi' := hf_spec i (lt_trans hij hj)
        have hj' := hf_spec j hj
        have hout : out_1[i]! < out_1[j]! := out_strict_mono hij hj
        have hnot_le : ¬ f j ≤ f i := by
          intro hle
          cases lt_or_eq_of_le hle with
          | inl hlt =>
              have hnums : nums[f j]! ≤ nums[f i]! := nums_mono hlt hi'.1
              have hout_le : out_1[j]! ≤ out_1[i]! := by
                simpa [hj'.2.symm, hi'.2.symm] using hnums
              exact (not_lt_of_ge hout_le) hout
          | inr heq =>
              have hout_eq : out_1[i]! = out_1[j]! := by
                calc
                  out_1[i]! = nums[f i]! := hi'.2
                  _ = nums[f j]! := by simpa [heq]
                  _ = out_1[j]! := hj'.2.symm
              exact (ne_of_lt hout) hout_eq
        exact lt_of_not_ge hnot_le
      · intro i hi j hj
        have hi' := hf_spec i hi
        have hf : f i = Nat.find (hexists i hi) := by
          simp [f, hi]
        intro hEq
        have hjSize : j < nums.size := lt_trans hj (by simpa [hf] using hi'.1)
        have pj : j < nums.size ∧ nums[j]! = out_1[i]! := ⟨hjSize, hEq⟩
        have hle : Nat.find (hexists i hi) ≤ j := Nat.find_le (h := hexists i hi) pj
        have : f i ≤ j := by simpa [hf] using hle
        exact (Nat.not_le_of_lt hj) this


prove_correct RemoveDuplicatesFromSortedArray by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i k out a a_1 invariant_inv_members_prefix if_pos_1)
  exact (goal_1 nums require_1 i k out invariant_inv_out_size a a_1 invariant_inv_last invariant_inv_strict if_pos if_neg_1)
  exact (goal_2 nums i k out invariant_inv_out_size a_1 invariant_inv_members_prefix if_pos)
  exact (goal_3 nums require_1 i_1 i_2 out_1 a_2 done_1 a a_1 invariant_inv_out_size invariant_inv_strict invariant_inv_members_prefix)
end Proof
