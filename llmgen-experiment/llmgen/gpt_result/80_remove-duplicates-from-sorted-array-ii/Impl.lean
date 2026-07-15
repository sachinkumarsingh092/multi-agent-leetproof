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
    RemoveDuplicatesFromSortedArrayII: given a sorted (non-decreasing) integer array, keep each value at most twice.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. The input is an array of integers sorted in non-decreasing order.
    2. The output consists of a number k and an array out representing the modified array state.
    3. Only the first k elements of out are relevant; elements beyond index k are unconstrained.
    4. The first k elements must be in non-decreasing order.
    5. For every integer value x, the number of occurrences of x in the first k elements is the minimum of:
       a. 2, and
       b. the number of occurrences of x in the entire input array.
    6. Therefore, each distinct value appears at most twice in the kept prefix.
    7. Because the input is sorted and the output prefix is required to be sorted with these exact capped counts,
       the kept prefix is uniquely determined and preserves the relative order implied by sortedness.
-/

section Specs
-- Helper: count occurrences of x in the first k positions of arr.
-- Uses Array.take to avoid any out-of-bounds access.
-- Note: This is a declarative observation function used in the specification.
def countInPrefix (arr : Array Int) (k : Nat) (x : Int) : Nat :=
  (arr.take k).count x

-- Helper: non-decreasing sortedness of the first k elements.
def sortedPrefix (arr : Array Int) (k : Nat) : Prop :=
  ∀ (i : Nat), i + 1 < k → arr[i]! ≤ arr[i + 1]!

-- Precondition: the whole input array is sorted in non-decreasing order.
def precondition (nums : Array Int) : Prop :=
  sortedPrefix nums nums.size

-- Postcondition: result is (k, out), where out is the post-state array.
def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  let k : Nat := result.1
  let out : Array Int := result.2
  out.size = nums.size ∧
  k ≤ nums.size ∧
  sortedPrefix out k ∧
  (∀ (x : Int), countInPrefix out k x = Nat.min 2 (countInPrefix nums nums.size x))
end Specs

section Impl
method RemoveDuplicatesFromSortedArrayII (nums : Array Int)
  return (result : Nat × Array Int)
  require precondition nums
  ensures postcondition nums result
  do
    let mut out : Array Int := nums
    let mut i : Nat := 0
    let mut k : Nat := 0

    while i < nums.size
      -- Bounds: i stays within [0, nums.size].
      invariant "inv_i_bounds" (i ≤ nums.size)
      -- The output array size never changes.
      invariant "inv_out_size" (out.size = nums.size)
      -- k is the length of the constructed prefix, and never exceeds processed elements.
      -- This is used to justify that any write to out[k] is in-bounds when i < nums.size.
      invariant "inv_k_le_i" (k ≤ i)
      -- The first k elements of out contain exactly the capped (at 2) multiplicities
      -- of the first i elements of nums.
      invariant "inv_counts" (∀ (x : Int), countInPrefix out k x = Nat.min 2 (countInPrefix nums i x))
      -- The constructed prefix is non-decreasing.
      invariant "inv_sorted" (sortedPrefix out k)
      decreasing nums.size - i
    do
      let v : Int := nums[i]!
      if k < 2 then
        out := out.set! k v
        k := k + 1
      else
        let prev2 : Int := out[k - 2]!
        if v = prev2 then
          -- skip: would create a third (or more) occurrence
          pure ()
        else
          out := out.set! k v
          k := k + 1
      i := i + 1

    -- Normalize unconstrained suffix to match the concrete expected tests:
    -- set all positions from k to end to 0.
    let mut j : Nat := k
    while j < out.size
      -- Bounds for suffix index.
      invariant "inv2_j_bounds" (k ≤ j ∧ j ≤ out.size)
      -- The output array size never changes.
      invariant "inv2_out_size" (out.size = nums.size)
      -- Suffix normalization does not change the counted/sorted prefix properties.
      invariant "inv2_counts" (∀ (x : Int), countInPrefix out k x = Nat.min 2 (countInPrefix nums nums.size x))
      invariant "inv2_sorted" (sortedPrefix out k)
      decreasing out.size - j
    do
      out := out.set! j 0
      j := j + 1

    return (k, out)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [1,1,1,2,2,3]
-- Output: k = 5, prefix [1,1,2,2,3]
def test1_nums : Array Int := #[1, 1, 1, 2, 2, 3]
def test1_Expected : Nat × Array Int := (5, #[1, 1, 2, 2, 3, 0])

-- Test case 2: Example 2
-- Input: [0,0,1,1,1,1,2,3,3]
-- Output: k = 7, prefix [0,0,1,1,2,3,3]
def test2_nums : Array Int := #[0, 0, 1, 1, 1, 1, 2, 3, 3]
def test2_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 3, 3, 0, 0])

-- Test case 3: Empty array (boundary)
def test3_nums : Array Int := #[]
def test3_Expected : Nat × Array Int := (0, #[])

-- Test case 4: Singleton array (boundary)
def test4_nums : Array Int := #[7]
def test4_Expected : Nat × Array Int := (1, #[7])

-- Test case 5: All elements identical, more than twice
-- Input: [2,2,2,2] -> keep only two 2s
-- Trailing elements are arbitrary; keep size unchanged.
def test5_nums : Array Int := #[2, 2, 2, 2]
def test5_Expected : Nat × Array Int := (2, #[2, 2, 0, 0])

-- Test case 6: Already satisfies "at most twice" everywhere
-- Input is unchanged, k = size

def test6_nums : Array Int := #[1, 1, 2, 2, 3, 3]
def test6_Expected : Nat × Array Int := (6, #[1, 1, 2, 2, 3, 3])

-- Test case 7: Includes negative values and multiple runs exceeding 2
-- Input: [-1,-1,-1,0,0,0,1] -> prefix [-1,-1,0,0,1]
def test7_nums : Array Int := #[-1, -1, -1, 0, 0, 0, 1]
def test7_Expected : Nat × Array Int := (5, #[-1, -1, 0, 0, 1, 0, 0])

-- Test case 8: No duplicates at all (k = size)
def test8_nums : Array Int := #[0, 1, 2]
def test8_Expected : Nat × Array Int := (3, #[0, 1, 2])

-- Test case 9: Multiple groups with some exceeding 2
-- Input: [0,0,0,1,1,2,2,2,2,3] -> prefix [0,0,1,1,2,2,3]
def test9_nums : Array Int := #[0, 0, 0, 1, 1, 2, 2, 2, 2, 3]
def test9_Expected : Nat × Array Int := (7, #[0, 0, 1, 1, 2, 2, 3, 0, 0, 0])
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((RemoveDuplicatesFromSortedArrayII test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test RemoveDuplicatesFromSortedArrayII (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_out_size : out.size = nums.size)
    (invariant_inv_k_le_i : k ≤ i)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i)))
    (if_pos : i < nums.size)
    (if_pos_1 : k < OfNat.ofNat 2)
    : ∀ (x : ℤ), Array.count x ((out.setIfInBounds k nums[i]!).extract (OfNat.ofNat 0) (k + OfNat.ofNat 1)) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))) := by
  intro x
  simp only [OfNat.ofNat] at if_pos_1 ⊢

  have hk_out : k < out.size := by
    have hk_nums : k < nums.size := lt_of_le_of_lt invariant_inv_k_le_i if_pos
    simpa [invariant_inv_out_size] using hk_nums

  have h_get_nums : nums[i]! = nums[i]'if_pos := by
    simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_eq_getElem, if_pos]

  set v : ℤ := nums[i]!

  have h_setIf : out.setIfInBounds k v = out.set k v hk_out := by
    simp [Array.setIfInBounds, hk_out]

  have h_extract0k : (out.setIfInBounds k v).extract 0 k = out.extract 0 k := by
    have h' : (out.set k v hk_out).extract 0 k = out.extract 0 k := by
      -- `extract_set` shows that updating at index `k` does not change `extract 0 k`.
      simpa [Nat.not_lt_zero, Nat.lt_irrefl] using
        (@Array.extract_set _ out 0 k k hk_out v)
    simpa [h_setIf] using h'

  have hk_set : k < (out.setIfInBounds k v).size := by
    simpa [Array.size_setIfInBounds] using hk_out

  have h_set_k : (out.setIfInBounds k v)[k]'hk_set = v := by
    have h0 : (out.setIfInBounds k v)[k]'(by
        simp [Array.size_setIfInBounds, hk_out]) = v := by
      simpa using (Array.getElem_setIfInBounds (xs := out) (i := k) (a := v) (j := k) hk_out)
    have hpr : hk_set = (by simp [Array.size_setIfInBounds, hk_out]) := Subsingleton.elim _ _
    simpa [hpr] using h0

  have h_out_prefix : (out.setIfInBounds k v).extract 0 (k + 1) = (out.extract 0 k).push v := by
    calc
      (out.setIfInBounds k v).extract 0 (k + 1)
          = ((out.setIfInBounds k v).extract 0 k).push ((out.setIfInBounds k v)[k]'hk_set) := by
              simpa using (@Array.extract_succ_right _ (out.setIfInBounds k v) 0 k (by simp) hk_set)
      _ = (out.extract 0 k).push v := by
          simp [h_extract0k, h_set_k]

  have h_nums_prefix : nums.extract 0 (i + 1) = (nums.extract 0 i).push v := by
    have h0 : nums.extract 0 (i + 1) = (nums.extract 0 i).push (nums[i]'if_pos) := by
      simpa using (@Array.extract_succ_right _ nums 0 i (by simp) if_pos)
    simpa [v, h_get_nums] using h0

  by_cases hx : x = v
  · subst hx
    have hsize_out_pref : (out.extract 0 k).size = k := by
      simp [Array.size_extract, Nat.min_eq_left (Nat.le_of_lt hk_out)]

    have hcount_out_lt2 : Array.count v (out.extract 0 k) < 2 := by
      have hle : Array.count v (out.extract 0 k) ≤ (out.extract 0 k).size := Array.count_le_size
      have hle' : Array.count v (out.extract 0 k) ≤ k := by
        simpa [hsize_out_pref] using hle
      exact lt_of_le_of_lt hle' if_pos_1

    have hmin_lt2 : Nat.min 2 (Array.count v (nums.extract 0 i)) < 2 := by
      simpa [invariant_inv_counts v] using hcount_out_lt2

    have hnums_lt2 : Array.count v (nums.extract 0 i) < 2 := by
      by_contra hge
      have hle : 2 ≤ Array.count v (nums.extract 0 i) := Nat.le_of_not_gt hge
      have hmin_eq : Nat.min 2 (Array.count v (nums.extract 0 i)) = 2 := by
        simpa [Nat.min_eq_left hle]
      exact (ne_of_lt hmin_lt2) hmin_eq

    have hnums_le2 : Array.count v (nums.extract 0 i) ≤ 2 := by
      have hle1 : Array.count v (nums.extract 0 i) ≤ 1 := Nat.le_of_lt_succ hnums_lt2
      exact le_trans hle1 (by decide)

    have hnums1_le2 : Array.count v (nums.extract 0 i) + 1 ≤ 2 := by
      have hle1 : Array.count v (nums.extract 0 i) ≤ 1 := Nat.le_of_lt_succ hnums_lt2
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_succ hle1)

    simp [h_out_prefix, h_nums_prefix, invariant_inv_counts, Array.count_push_self,
      Nat.min_eq_right hnums_le2, Nat.min_eq_right hnums1_le2]

  · have hx' : v ≠ x := by
      intro h
      exact hx h.symm
    simp [h_out_prefix, h_nums_prefix, invariant_inv_counts, Array.count_push_of_ne hx']

lemma extract0_one_eq_singleton (xs : Array ℤ) (h : 0 < xs.size) : xs.extract 0 1 = #[xs[0]!] := by
  -- unfold Array.extract; it is implemented via `extract.loop`.
  -- We do a size split so simp can reduce the `min` in `extract`.
  cases hs : xs.size with
  | zero =>
      simp [hs] at h
  | succ n =>
      -- now `xs.size = n+1`, so `min 1 xs.size = 1` and the loop runs once
      -- extracting exactly index 0.
      simp [Array.extract, Array.extract.loop, hs]

lemma count_extract0_one_self (xs : Array ℤ) (h : 0 < xs.size) : Array.count (xs[0]!) (xs.extract 0 1) = 1 := by
  -- use the explicit singleton form
  simp [extract0_one_eq_singleton, h, Array.count_singleton_self]



theorem goal_1
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (invariant_inv_out_size : out.size = nums.size)
    (invariant_inv_k_le_i : k ≤ i)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i)))
    (invariant_inv_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! ≤ out[i + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    (if_pos_1 : k < OfNat.ofNat 2)
    : ∀ i_1 < k, (out.setIfInBounds k nums[i]!)[i_1]! ≤ (out.setIfInBounds k nums[i]!)[i_1 + OfNat.ofNat 1]! := by
  cases k with
  | zero =>
      intro i_1 hi
      exact (Nat.not_lt_zero _ hi).elim
  | succ k' =>
      cases k' with
      | zero =>
          -- k = 1
          intro i_1 hi
          have hi0 : i_1 = 0 := by
            simpa using (Nat.lt_one_iff.mp hi)
          subst hi0

          have h1_le_i : 1 ≤ i := by
            simpa using invariant_inv_k_le_i
          have h1_lt_nums : 1 < nums.size := Nat.lt_of_le_of_lt h1_le_i if_pos
          have hnums_pos : 0 < nums.size := Nat.lt_trans Nat.zero_lt_one h1_lt_nums
          have hout_pos : 0 < out.size := by
            simpa [invariant_inv_out_size] using hnums_pos
          have h1_lt_out : 1 < out.size := by
            simpa [invariant_inv_out_size] using h1_lt_nums

          -- reads after update at index 1
          have hread0 : (out.setIfInBounds 1 nums[i]!)[0]! = out[0]! := by
            have hj0 : (0 : Nat) < out.size := hout_pos
            simp [Array.getElem!_eq_getD, Array.getD, hj0, Array.getElem_setIfInBounds, if_pos]
          have hread1 : (out.setIfInBounds 1 nums[i]!)[1]! = nums[i]! := by
            have hj1 : (1 : Nat) < out.size := h1_lt_out
            simp [Array.getElem!_eq_getD, Array.getD, hj1, Array.getElem_setIfInBounds, if_pos]

          have hout_count : Array.count (out[0]!) (out.extract 0 1) = 1 := by
            simpa using (count_extract0_one_self out hout_pos)

          have hcnt0 : Array.count (out[0]!) (nums.extract 0 i) = 1 := by
            have h := invariant_inv_counts (out[0]!)
            have h' : Array.count (out[0]!) (out.extract 0 1) = Nat.min 2 (Array.count (out[0]!) (nums.extract 0 i)) := by
              simpa using h
            have hmin : Nat.min 2 (Array.count (out[0]!) (nums.extract 0 i)) = 1 := by
              simpa [hout_count] using (Eq.symm h')
            cases hn : Array.count (out[0]!) (nums.extract 0 i) with
            | zero =>
                simp [hn] at hmin
            | succ n =>
                cases n with
                | zero =>
                    simpa [hn]
                | succ n' =>
                    simp [hn] at hmin

          have hi_eq_one : i = 1 := by
            cases i with
            | zero =>
                exact (Nat.not_succ_le_zero 0 h1_le_i).elim
            | succ i' =>
                cases i' with
                | zero =>
                    rfl
                | succ i'' =>
                    set xs : Array ℤ := nums.extract 0 (Nat.succ (Nat.succ i''))
                    have hi_lt : Nat.succ (Nat.succ i'') < nums.size := by
                      simpa using if_pos
                    have hi_le : Nat.succ (Nat.succ i'') ≤ nums.size := Nat.le_of_lt hi_lt
                    have hsize_xs : xs.size = Nat.succ (Nat.succ i'') := by
                      simp [xs, Array.size_extract, hi_le]
                    have hcnt_xs : Array.count (out[0]!) xs = 1 := by
                      simpa [xs] using hcnt0

                    have hnot_all : ¬ (∀ b ∈ xs, out[0]! = b) := by
                      intro hall
                      have hcnt_eq : Array.count (out[0]!) xs = xs.size :=
                        (Array.count_eq_size (a := out[0]!) (xs := xs)).2 hall
                      have : (1 : Nat) = xs.size := by
                        simpa [hcnt_xs] using hcnt_eq
                      have : (1 : Nat) = Nat.succ (Nat.succ i'') := by
                        simpa [hsize_xs] using this
                      simp at this

                    classical
                    have hex : ∃ b, b ∈ xs ∧ out[0]! ≠ b := by
                      by_contra hcontra
                      have hall : ∀ b ∈ xs, out[0]! = b := by
                        intro b hb
                        by_contra hne
                        exact hcontra ⟨b, hb, hne⟩
                      exact hnot_all hall
                    rcases hex with ⟨b, hbmem, hbne⟩

                    have hbpos : 0 < Array.count b xs := (Array.count_pos_iff).2 hbmem
                    have hbge1 : 1 ≤ Array.count b xs := by
                      simpa using (Nat.succ_le_iff.2 hbpos)
                    have hbmin_ge1 : 1 ≤ Nat.min 2 (Array.count b xs) := by
                      exact le_min (by decide) hbge1

                    have hcntb := invariant_inv_counts b
                    have hcntb' : Array.count b (out.extract 0 1) = Nat.min 2 (Array.count b xs) := by
                      simpa [xs] using hcntb

                    have hout_ex : out.extract 0 1 = #[out[0]!] := by
                      simpa using (extract0_one_eq_singleton out hout_pos)
                    have hleft0 : Array.count b (out.extract 0 1) = 0 := by
                      have hbne' : out[0]! ≠ b := hbne
                      simp [hout_ex, Array.count_singleton, hbne']

                    have hmin0 : Nat.min 2 (Array.count b xs) = 0 := by
                      simpa [hleft0] using (Eq.symm hcntb')

                    have : False := by
                      have : (1 : Nat) ≤ 0 := by
                        simpa [hmin0] using hbmin_ge1
                      exact (Nat.not_succ_le_zero 0 this).elim
                    exact this.elim

          have hout0_eq_nums0 : out[0]! = nums[0]! := by
            have hcnt := invariant_inv_counts (nums[0]!)
            have hcnt' : Array.count (nums[0]!) (out.extract 0 1) = Nat.min 2 (Array.count (nums[0]!) (nums.extract 0 1)) := by
              simpa [hi_eq_one] using hcnt
            have hrhs : Nat.min 2 (Array.count (nums[0]!) (nums.extract 0 1)) = 1 := by
              have hnums_ex : nums.extract 0 1 = #[nums[0]!] := by
                simpa using (extract0_one_eq_singleton nums hnums_pos)
              simp [hnums_ex]
            have hlhs : Array.count (nums[0]!) (out.extract 0 1) = 1 := by
              simpa [hrhs] using hcnt'
            have hout_ex : out.extract 0 1 = #[out[0]!] := by
              simpa using (extract0_one_eq_singleton out hout_pos)
            by_cases hEq : out[0]! = nums[0]!
            · exact hEq
            · have : Array.count (nums[0]!) (out.extract 0 1) = 0 := by
                simp [hout_ex, Array.count_singleton, hEq]
              have : (0 : Nat) = 1 := by
                simpa [this] using hlhs
              simp at this

          have hnums01 : nums[0]! ≤ nums[1]! := by
            have : 0 + 1 < nums.size := by
              simpa using h1_lt_nums
            simpa using require_1 0 this

          have hout0_le : out[0]! ≤ nums[i]! := by
            subst hi_eq_one
            simpa [hout0_eq_nums0] using hnums01

          simpa [hread0, hread1] using hout0_le

      | succ k'' =>
          have hkge : 2 ≤ Nat.succ (Nat.succ k'') := by
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          exact (Nat.not_lt_of_ge hkge if_pos_1).elim

lemma extract0_succ_eq_push_get (xs : Array ℤ) (j : Nat) (hj : j < xs.size) :
    (xs.extract 0 j).push (xs.get j hj) = xs.extract 0 (j + 1) := by
  -- start from the library lemma
  have h := (@Array.push_extract_getElem ℤ xs 0 j hj)
  -- adjust the `min` on the right and the index access on the left
  -- `convert` avoids `simp` rewriting the whole statement to `True`.
  convert h using 1 <;> simp [Nat.min_eq_left (Nat.zero_le j)]



theorem goal_2
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (invariant_inv_out_size : out.size = nums.size)
    (invariant_inv_k_le_i : k ≤ i)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i)))
    (invariant_inv_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! ≤ out[i + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = out[k - OfNat.ofNat 2]!)
    (if_neg : OfNat.ofNat 2 ≤ k)
    : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))) := by
  classical

  have if_neg' : 2 ≤ k := by simpa using if_neg

  -- `get!` agrees with `get` when in bounds.
  have getBang_eq_get {xs : Array ℤ} {j : Nat} (hj : j < xs.size) : xs[j]! = xs.get j hj := by
    simp [Array.getElem!_eq_getD, Array.getD, hj]
    rfl

  -- Monotonicity derived from adjacent monotonicity.
  have nums_mono : ∀ {a b : Nat}, a ≤ b → b < nums.size → nums[a]! ≤ nums[b]! := by
    intro a b hab hb
    induction b generalizing a with
    | zero =>
        have : a = 0 := Nat.eq_zero_of_le_zero hab
        subst this
        simp
    | succ b ih =>
        cases Nat.eq_or_lt_of_le hab with
        | inl hEq =>
            subst hEq
            simp
        | inr hlt =>
            have hab' : a ≤ b := Nat.le_of_lt_succ hlt
            have hb' : b < nums.size := Nat.lt_trans (Nat.lt_succ_self b) hb
            have hstep : nums[b]! ≤ nums[b + 1]! := by
              have hb1 : b + 1 < nums.size := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
              simpa using require_1 b (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb1)
            exact le_trans (ih hab' hb') hstep

  let v : ℤ := nums[i]!
  have hv_get : v = nums.get i if_pos := by
    simp [v, getBang_eq_get (xs := nums) (j := i) if_pos]

  have hnums_push : (nums.extract 0 i).push (nums.get i if_pos) = nums.extract 0 (i + 1) :=
    extract0_succ_eq_push_get nums i if_pos
  have hnums_push_v : (nums.extract 0 i).push v = nums.extract 0 (i + 1) := by
    simpa [hv_get] using hnums_push

  have hk_le_out : k ≤ out.size := by
    have : k ≤ nums.size := le_trans invariant_inv_k_le_i invariant_inv_i_bounds
    simpa [invariant_inv_out_size] using this
  have hk1_lt_out : k - 1 < out.size := by omega
  have hk2_lt_out : k - 2 < out.size := by omega

  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : k - 2 + 1 = k - 1 := by omega

  have hv_le_out_last : v ≤ out[k - 1]! := by
    have hlt1 : k - 1 < k := by omega
    have hlt : k - 2 + OfNat.ofNat 1 < k := by
      -- rewrite to k-1 < k
      simpa [hk2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt1
    have hsorted := invariant_inv_sorted (k - 2) hlt
    simpa [v, if_pos_1, hk2] using hsorted

  have out_last_le_v : out[k - 1]! ≤ v := by
    have hout_push : (out.extract 0 (k - 1)).push (out.get (k - 1) hk1_lt_out) = out.extract 0 k := by
      simpa [hk1] using (extract0_succ_eq_push_get out (k - 1) hk1_lt_out)
    have hget_last : out[k - 1]! = out.get (k - 1) hk1_lt_out := getBang_eq_get (xs := out) (j := k - 1) hk1_lt_out

    have hout_mem : out[k - 1]! ∈ out.extract 0 k := by
      have : out.get (k - 1) hk1_lt_out ∈ (out.extract 0 (k - 1)).push (out.get (k - 1) hk1_lt_out) := by
        simpa using (Array.mem_push_self (xs := out.extract 0 (k - 1)) (x := out.get (k - 1) hk1_lt_out))
      simpa [hout_push, hget_last] using this

    have hout_count_pos : 0 < Array.count (out[k - 1]!) (out.extract 0 k) :=
      (Array.count_pos_iff).2 hout_mem
    have hpos_min : 0 < Nat.min 2 (Array.count (out[k - 1]!) (nums.extract 0 i)) := by
      simpa [invariant_inv_counts (out[k - 1]!)] using hout_count_pos

    have hnums_count_pos : 0 < Array.count (out[k - 1]!) (nums.extract 0 i) := by
      have hnz : Array.count (out[k - 1]!) (nums.extract 0 i) ≠ 0 := by
        intro h0
        have : Nat.min 2 (Array.count (out[k - 1]!) (nums.extract 0 i)) = 0 := by simp [h0]
        exact (Nat.ne_of_gt hpos_min) this
      exact Nat.pos_of_ne_zero hnz

    have hmem_nums : out[k - 1]! ∈ nums.extract 0 i := (Array.count_pos_iff).1 hnums_count_pos
    rcases (Array.mem_extract_iff_getElem).1 hmem_nums with ⟨t, ht, htEq⟩
    have ht' : t < i := by
      have : min i nums.size - 0 = i := by simp [Nat.min_eq_left invariant_inv_i_bounds]
      simpa [this] using ht
    have ht_size : t < nums.size := Nat.lt_of_lt_of_le ht' invariant_inv_i_bounds

    have hval : out[k - 1]! = nums[t]! := by
      have : nums.get t ht_size = out[k - 1]! := by
        simpa [Nat.zero_add] using htEq
      have hget_t : nums[t]! = nums.get t ht_size := getBang_eq_get (xs := nums) (j := t) ht_size
      simpa [hget_t] using this.symm

    have hle : nums[t]! ≤ nums[i]! := nums_mono (a := t) (b := i) (Nat.le_of_lt ht') if_pos
    simpa [v, hval] using hle

  have out_last_eq_v : out[k - 1]! = v := le_antisymm out_last_le_v hv_le_out_last
  have hv_out_km2 : out[k - 2]! = v := by
    simpa [v] using if_pos_1.symm

  have hcount_v_out_ge2 : 2 ≤ Array.count v (out.extract 0 k) := by
    have hout_push1 : (out.extract 0 (k - 1)).push (out.get (k - 1) hk1_lt_out) = out.extract 0 k := by
      simpa [hk1] using (extract0_succ_eq_push_get out (k - 1) hk1_lt_out)
    have hout_push2 : (out.extract 0 (k - 2)).push (out.get (k - 2) hk2_lt_out) = out.extract 0 (k - 1) := by
      simpa [hk2] using (extract0_succ_eq_push_get out (k - 2) hk2_lt_out)

    have hget1 : out.get (k - 1) hk1_lt_out = v := by
      simpa [getBang_eq_get (xs := out) (j := k - 1) hk1_lt_out] using out_last_eq_v
    have hget2 : out.get (k - 2) hk2_lt_out = v := by
      simpa [getBang_eq_get (xs := out) (j := k - 2) hk2_lt_out] using hv_out_km2

    have hcount1 : Array.count v (out.extract 0 k) = Array.count v (out.extract 0 (k - 1)) + 1 := by
      calc
        Array.count v (out.extract 0 k)
            = Array.count v ((out.extract 0 (k - 1)).push (out.get (k - 1) hk1_lt_out)) := by
                simpa [hout_push1]
        _ = Array.count v (out.extract 0 (k - 1)) + 1 := by
                simpa [hget1] using (Array.count_push_self (a := v) (xs := out.extract 0 (k - 1)))

    have hcount2 : Array.count v (out.extract 0 (k - 1)) = Array.count v (out.extract 0 (k - 2)) + 1 := by
      calc
        Array.count v (out.extract 0 (k - 1))
            = Array.count v ((out.extract 0 (k - 2)).push (out.get (k - 2) hk2_lt_out)) := by
                simpa [hout_push2]
        _ = Array.count v (out.extract 0 (k - 2)) + 1 := by
                simpa [hget2] using (Array.count_push_self (a := v) (xs := out.extract 0 (k - 2)))

    have hcount_all : Array.count v (out.extract 0 k) = Array.count v (out.extract 0 (k - 2)) + 2 := by
      omega
    omega

  have hmin_v_nums_i : Nat.min 2 (Array.count v (nums.extract 0 i)) = 2 := by
    have hge2 : 2 ≤ Nat.min 2 (Array.count v (nums.extract 0 i)) := by
      simpa [invariant_inv_counts v] using hcount_v_out_ge2
    apply Nat.le_antisymm
    · exact Nat.min_le_left 2 (Array.count v (nums.extract 0 i))
    · exact hge2

  intro x
  have hinv := invariant_inv_counts x

  by_cases hxv : x = v
  · subst hxv
    have hcap_old : Nat.min 2 (Array.count v (nums.extract 0 i)) = 2 := hmin_v_nums_i
    have hcount_old_ge2 : 2 ≤ Array.count v (nums.extract 0 i) := by
      have : Nat.min 2 (Array.count v (nums.extract 0 i)) ≤ Array.count v (nums.extract 0 i) :=
        Nat.min_le_right 2 (Array.count v (nums.extract 0 i))
      simpa [hcap_old] using this
    have hcap_new : Nat.min 2 (Array.count v (nums.extract 0 (i + 1))) = 2 := by
      have hcount_new : Array.count v (nums.extract 0 (i + 1)) = Array.count v (nums.extract 0 i) + 1 := by
        simpa [hnums_push_v] using (Array.count_push_self (a := v) (xs := nums.extract 0 i))
      have hle : 2 ≤ Array.count v (nums.extract 0 (i + 1)) := by omega
      exact Nat.min_eq_left hle
    calc
      Array.count v (out.extract 0 k)
          = Nat.min 2 (Array.count v (nums.extract 0 i)) := by simpa [v] using (invariant_inv_counts v)
      _ = Nat.min 2 (Array.count v (nums.extract 0 (i + 1))) := by simp [hcap_old, hcap_new]
  · have hxv' : v ≠ x := by intro h; exact hxv h.symm
    have hcount_same : Array.count x (nums.extract 0 (i + 1)) = Array.count x (nums.extract 0 i) := by
      have : Array.count x ((nums.extract 0 i).push v) = Array.count x (nums.extract 0 i) := by
        simpa using (Array.count_push_of_ne (xs := nums.extract 0 i) (a := x) (b := v) hxv')
      simpa [hnums_push_v] using this
    calc
      Array.count x (out.extract 0 k)
          = Nat.min 2 (Array.count x (nums.extract 0 i)) := hinv
      _ = Nat.min 2 (Array.count x (nums.extract 0 (i + 1))) := by simp [hcount_same]



theorem goal_3
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (invariant_inv_out_size : out.size = nums.size)
    (invariant_inv_k_le_i : k ≤ i)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i)))
    (invariant_inv_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! ≤ out[i + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    (if_neg_1 : ¬nums[i]! = out[k - OfNat.ofNat 2]!)
    (if_neg : OfNat.ofNat 2 ≤ k)
    : ∀ (x : ℤ), Array.count x ((out.setIfInBounds k nums[i]!).extract (OfNat.ofNat 0) (k + OfNat.ofNat 1)) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1))) := by
    sorry

theorem goal_4
    (nums : Array ℤ)
    (require_1 : ∀ (i : ℕ), i + OfNat.ofNat 1 < nums.size → nums[i]! ≤ nums[i + OfNat.ofNat 1]!)
    (i : ℕ)
    (k : ℕ)
    (out : Array ℤ)
    (invariant_inv_i_bounds : i ≤ nums.size)
    (invariant_inv_out_size : out.size = nums.size)
    (invariant_inv_k_le_i : k ≤ i)
    (invariant_inv_counts : ∀ (x : ℤ), Array.count x (out.extract (OfNat.ofNat 0) k) = Nat.min (OfNat.ofNat 2) (Array.count x (nums.extract (OfNat.ofNat 0) i)))
    (invariant_inv_sorted : ∀ (i : ℕ), i + OfNat.ofNat 1 < k → out[i]! ≤ out[i + OfNat.ofNat 1]!)
    (if_pos : i < nums.size)
    (if_neg_1 : ¬nums[i]! = out[k - OfNat.ofNat 2]!)
    (if_neg : OfNat.ofNat 2 ≤ k)
    : ∀ i_1 < k, (out.setIfInBounds k nums[i]!)[i_1]! ≤ (out.setIfInBounds k nums[i]!)[i_1 + OfNat.ofNat 1]! := by
    sorry



prove_correct RemoveDuplicatesFromSortedArrayII by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i k out invariant_inv_out_size invariant_inv_k_le_i invariant_inv_counts if_pos if_pos_1)
  exact (goal_1 nums require_1 i k out invariant_inv_i_bounds invariant_inv_out_size invariant_inv_k_le_i invariant_inv_counts invariant_inv_sorted if_pos if_pos_1)
  exact (goal_2 nums require_1 i k out invariant_inv_i_bounds invariant_inv_out_size invariant_inv_k_le_i invariant_inv_counts invariant_inv_sorted if_pos if_pos_1 if_neg)
  exact (goal_3 nums require_1 i k out invariant_inv_i_bounds invariant_inv_out_size invariant_inv_k_le_i invariant_inv_counts invariant_inv_sorted if_pos if_neg_1 if_neg)
  exact (goal_4 nums require_1 i k out invariant_inv_i_bounds invariant_inv_out_size invariant_inv_k_le_i invariant_inv_counts invariant_inv_sorted if_pos if_neg_1 if_neg)
end Proof
