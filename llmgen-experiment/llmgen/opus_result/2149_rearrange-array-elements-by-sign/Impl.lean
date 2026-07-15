import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/- Problem Description
    2149. Rearrange Array Elements by Sign: Rearrange an even-length integer array with equal numbers of positive and negative elements so that signs alternate starting with a positive, while preserving relative order within each sign.
    **Important: complexity should be O(n) time and O(n) space**
    Natural language breakdown:
    1. The input is a 0-indexed array of integers of even length.
    2. Every element is either strictly positive or strictly negative (no zeros).
    3. The number of positive elements equals the number of negative elements.
    4. The output is an array of the same length that is a rearrangement (permutation) of the input.
    5. The output starts with a positive element when the array is nonempty.
    6. Consecutive elements in the output have opposite signs (equivalently, indices with even parity are positive and odd parity are negative).
    7. Among all positives (respectively negatives), their relative order in the output is the same as in the input (stable with respect to sign).
-/

section Specs
-- Helper predicates as Bool for use with Array.filter/countP.
def isPosB (x : Int) : Bool := decide (x > 0)
def isNegB (x : Int) : Bool := decide (x < 0)

def countPos (nums : Array Int) : Nat := nums.countP isPosB

def countNeg (nums : Array Int) : Nat := nums.countP isNegB

def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

-- Parity-based sign pattern for the desired result.
def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

-- Stable order within sign can be characterized by equality of the sign-filtered subsequences.
def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

-- Preconditions: even length, no zeros, equal number of positives and negatives.
def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

-- Postconditions: permutation, correct alternating sign pattern, starts with positive if nonempty,
-- and stability of relative order within each sign.
def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result
end Specs

section Impl
method RearrangeArrayElementsBySign (nums : Array Int)
  return (result : Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  -- Step 1: Collect positives and negatives separately (preserving order)
  let mut positives : Array Int := #[]
  let mut negatives : Array Int := #[]
  let mut i : Nat := 0
  while i < nums.size
    -- i is bounded by array size
    -- Init: i=0 ≤ nums.size. Pres: i increments up to nums.size. Suff: with ¬(i < nums.size), i = nums.size.
    invariant "i_bound" i ≤ nums.size
    -- positives are exactly the positive-filtered prefix nums[0..i]
    -- Init: extract 0 0 = #[], filter of #[] = #[] = positives. Pres: push if v>0 matches filter behavior.
    invariant "pos_eq_filter" positives = (nums.extract 0 i).filter isPosB
    -- negatives are exactly the negative-filtered prefix nums[0..i]
    -- Init: same as above. Pres: push if v≤0 (and v≠0 by precondition) means v<0, matches isNegB filter.
    invariant "neg_eq_filter" negatives = (nums.extract 0 i).filter isNegB
    decreasing nums.size - i
  do
    let v := nums[i]!
    if v > 0 then
      positives := positives.push v
    else
      negatives := negatives.push v
    i := i + 1

  -- Step 2: Interleave into result array
  -- Even indices get positives, odd indices get negatives
  let mut res : Array Int := Array.replicate nums.size (0 : Int)
  let mut pi : Nat := 0
  let mut ni : Nat := 0
  let mut j : Nat := 0
  while j < nums.size
    -- j is bounded
    -- Init: j=0 ≤ nums.size. Pres: j increments. Suff: j = nums.size at exit.
    invariant "j_bound" j ≤ nums.size
    -- res size is preserved through set! operations
    -- Init: Array.replicate produces array of nums.size. Pres: set! preserves size.
    invariant "res_size" res.size = nums.size
    -- pi = number of even indices in [0, j), which is ⌈j/2⌉ = (j+1)/2
    -- Init: pi=0 = (0+1)/2 = 0. Pres: pi increments on even j.
    invariant "pi_val" pi = (j + 1) / 2
    -- ni = number of odd indices in [0, j), which is ⌊j/2⌋ = j/2
    -- Init: ni=0 = 0/2 = 0. Pres: ni increments on odd j.
    invariant "ni_val" ni = j / 2
    -- For even indices < j, the result holds the corresponding positive element
    -- Init: vacuously true. Pres: set! at j with positives[pi]!, other indices unchanged.
    invariant "even_filled" ∀ k : Nat, k < j → k % 2 = 0 → res[k]! = positives[k / 2]!
    -- For odd indices < j, the result holds the corresponding negative element
    -- Init: vacuously true. Pres: set! at j with negatives[ni]!, other indices unchanged.
    invariant "odd_filled" ∀ k : Nat, k < j → k % 2 = 1 → res[k]! = negatives[k / 2]!
    -- After loop 1 completed, positives = full positive filter of nums
    -- These are frame invariants (not modified in loop 2).
    invariant "pos_full" positives = nums.filter isPosB
    invariant "neg_full" negatives = nums.filter isNegB
    -- Size invariants derived from precondition and the above
    invariant "pos_size" positives.size = nums.size / 2
    invariant "neg_size" negatives.size = nums.size / 2
    decreasing nums.size - j
  do
    if j % 2 = 0 then
      res := res.set! j (positives[pi]!)
      pi := pi + 1
    else
      res := res.set! j (negatives[ni]!)
      ni := ni + 1
    j := j + 1

  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: [3,1,-2,-5,2,-4]
-- Output: [3,-2,1,-5,2,-4]
def test1_nums : Array Int := #[3, 1, -2, -5, 2, -4]
def test1_Expected : Array Int := #[3, -2, 1, -5, 2, -4]

-- Test case 2: Example 2 (starts with a negative in input)
def test2_nums : Array Int := #[-1, 1]
def test2_Expected : Array Int := #[1, -1]

-- Test case 3: Empty array (degenerate but satisfies even length and equal counts)
def test3_nums : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: Smallest nontrivial already-correct alternating order
def test4_nums : Array Int := #[1, -1]
def test4_Expected : Array Int := #[1, -1]

-- Test case 5: Larger array where positives/negatives are grouped
-- Positives: [1,2,3], Negatives: [-1,-2,-3]
def test5_nums : Array Int := #[1, 2, 3, -1, -2, -3]
def test5_Expected : Array Int := #[1, -1, 2, -2, 3, -3]

-- Test case 6: Alternating input but begins with negative; must start with positive in output
-- Positives: [5,6], Negatives: [-5,-6]
def test6_nums : Array Int := #[-5, 5, -6, 6]
def test6_Expected : Array Int := #[5, -5, 6, -6]

-- Test case 7: Mixed order; checks stability within each sign
-- Positives in input: [2,4,6,8], Negatives: [-1,-3,-5,-7]
def test7_nums : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]
def test7_Expected : Array Int := #[2, -1, 4, -3, 6, -5, 8, -7]

-- Test case 8: All positives first but with different magnitudes; confirms stable order
-- Positives: [10,1,7], Negatives: [-2,-9,-3]
def test8_nums : Array Int := #[10, 1, 7, -2, -9, -3]
def test8_Expected : Array Int := #[10, -2, 1, -9, 7, -3]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((RearrangeArrayElementsBySign test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((RearrangeArrayElementsBySign test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((RearrangeArrayElementsBySign test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((RearrangeArrayElementsBySign test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((RearrangeArrayElementsBySign test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((RearrangeArrayElementsBySign test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((RearrangeArrayElementsBySign test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((RearrangeArrayElementsBySign test8_nums).run), DivM.res test8_Expected ]
end Assertions

section Pbt
velvet_plausible_test RearrangeArrayElementsBySign (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (invariant_i_bound : i ≤ nums.size)
    (if_pos : i < nums.size)
    (if_pos_1 : OfNat.ofNat 0 < nums[i]!)
    : (Array.filter isPosB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)).push nums[i]! = Array.filter isPosB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
    -- Simplify getElem! to getElem
    have h_getelem : nums[i]! = nums[i]'if_pos := by
      simp [Array.getElem!_eq_getD, Array.getD, dif_pos if_pos]
    have h_min_i : min i nums.size = i := by omega
    have h_min_i1 : min (i + 1) nums.size = i + 1 := by omega
    rw [h_min_i, h_min_i1, h_getelem]
    have h_size_extract : (nums.extract 0 i).size = i := by
      simp [Array.size_extract]; omega
    -- push_extract_getElem: (as.extract i j).push as[j] = as.extract (min i j) (j + 1)
    have h_extract_push : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
      have h := @Array.push_extract_getElem ℤ nums 0 i if_pos
      simp only [Nat.zero_min, Nat.zero_le, Nat.min_eq_left] at h
      exact h
    -- We need isPosB (nums[i]) = true
    have h_pos : isPosB (nums[i]'if_pos) = true := by
      simp only [isPosB, decide_eq_true_eq]
      rw [h_getelem] at if_pos_1
      exact if_pos_1
    -- Use filter_push_of_pos
    have h_filter_push := Array.filter_push_of_pos h_pos (show (nums.extract 0 i).size + 1 = (nums.extract 0 i).size + 1 from rfl)
    rw [h_size_extract] at h_filter_push
    -- h_filter_push : filter isPosB ((extract 0 i).push nums[i]) 0 (i + 1) = (filter isPosB (extract 0 i)).push nums[i]
    rw [← h_extract_push, h_filter_push]

theorem goal_1
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : OfNat.ofNat 0 < nums[i]!)
    : Array.filter isNegB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) = Array.filter isNegB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
    have h_bang_eq : nums[i]! = nums[i] := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, if_pos]
    have h_extract_succ : nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i] := by
      exact Array.extract_succ_right (by omega) if_pos
    have h_not_neg : ¬isNegB nums[i] := by
      simp [isNegB]
      rw [← h_bang_eq]
      omega
    have h_stop_eq : min (i + 1) nums.size = (nums.extract 0 i).size + 1 := by
      simp [Array.size_extract]; omega
    rw [h_extract_succ]
    rw [Array.filter_push_of_neg h_not_neg h_stop_eq]
    congr 1
    simp [Array.size_extract]

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : nums[i]! ≤ OfNat.ofNat 0)
    : Array.filter isPosB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size) = Array.filter isPosB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
    have hi_le : i ≤ nums.size := Nat.le_of_lt if_pos
    have hi1_le : i + 1 ≤ nums.size := if_pos
    simp only [Nat.min_eq_left hi_le, Nat.min_eq_left hi1_le]
    have hsize : (nums.extract 0 i).size = i := by
      simp [Array.size_extract, Nat.min_eq_left hi_le]
    -- extract 0 (i+1) = (extract 0 i).push nums[i]
    have hextract : nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i] := by
      have h := @Array.push_extract_getElem _ nums 0 i if_pos
      simp only [Nat.min_eq_left hi_le, Nat.zero_le, min_eq_left] at h
      exact h.symm
    -- isPosB on nums[i] is false
    have hnotpos : ¬ isPosB nums[i] := by
      simp only [isPosB, decide_eq_true_eq, not_lt]
      have h_eq : nums[i]! = nums[i] := by
        simp [Array.getElem!_eq_getD, Array.getD, if_pos, dite_true]
      linarith
    rw [hextract]
    rw [Array.filter_push_of_neg hnotpos (by omega)]
    congr 1
    exact hsize.symm

theorem goal_3
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i : ℕ)
    (invariant_i_bound : i ≤ nums.size)
    (if_pos : i < nums.size)
    (if_neg : nums[i]! ≤ OfNat.ofNat 0)
    : (Array.filter isNegB (nums.extract (OfNat.ofNat 0) i) (OfNat.ofNat 0) (min i nums.size)).push nums[i]! = Array.filter isNegB (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) (OfNat.ofNat 0) (min (i + OfNat.ofNat 1) nums.size) := by
    have h_bang : nums[i]! = nums[i] := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?]
      simp [show i < nums.size from if_pos]
    have h_nonzero := require_1.2.1 i if_pos
    have h_neg : nums[i]! < 0 := by
      rw [h_bang]
      have h1 : ¬(nums[i] : ℤ) = (0 : ℤ) := by rwa [← h_bang]
      have h2 : (nums[i] : ℤ) ≤ (0 : ℤ) := by rwa [h_bang] at if_neg
      omega
    have h_isNeg : isNegB nums[i]! = true := by
      simp [isNegB]; exact h_neg
    have h_extract : nums.extract 0 (i + 1) = (nums.extract 0 i).push nums[i] := by
      have h1 := @Array.push_extract_getElem ℤ nums 0 i if_pos
      simp only [Nat.zero_le, Nat.min_eq_left] at h1
      exact h1.symm
    have h_size_extract : (nums.extract 0 i).size = i := by
      simp [Array.size_extract]; omega
    have h_min1 : min i nums.size = i := by omega
    have h_min2 : min (i + 1) nums.size = i + 1 := by omega
    have h_isNeg2 : isNegB nums[i] = true := by rw [← h_bang]; exact h_isNeg
    simp only [h_min1, h_min2]
    -- Goal: (filter isNegB (extract 0 i) 0 i).push nums[i]! = filter isNegB (extract 0 (i+1)) 0 (i+1)
    rw [h_extract, h_bang]
    rw [Array.filter_push_of_pos h_isNeg2 (by rw [h_size_extract])]
    -- Now need: filter isNegB (extract 0 i) 0 i = filter isNegB (extract 0 i)
    congr 1
    simp [h_size_extract]

theorem goal_4
    (nums : Array ℤ)
    (i_1 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size) = Array.filter isPosB nums := by
    have h_eq : i_1 = nums.size := Nat.le_antisymm invariant_i_bound done_1
    subst h_eq
    simp [Array.extract_size, min_self]

theorem goal_5
    (nums : Array ℤ)
    (i_1 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size) = Array.filter isNegB nums := by
    have hi : i_1 = nums.size := Nat.le_antisymm invariant_i_bound done_1
    subst hi
    simp [Array.extract_size, min_self]

theorem goal_6
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : (Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)).size = nums.size / OfNat.ofNat 2 := by
    have h4 := goal_4 nums i_1 invariant_i_bound done_1
    rw [h4]
    have hcp := require_1.2.2.1
    rw [Array.countP_eq_size_filter] at hcp
    exact hcp

theorem goal_7
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (done_1 : nums.size ≤ i_1)
    : (Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size)).size = nums.size / OfNat.ofNat 2 := by
    have h_eq : i_1 = nums.size := Nat.le_antisymm invariant_i_bound done_1
    subst h_eq
    simp [Array.extract_size, Nat.min_self]
    have h_countP := require_1.2.2.2
    rw [Array.countP_eq_size_filter] at h_countP
    exact h_countP

theorem goal_8_0_0
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (h_neg_is_not_pos : ∀ (x : ℤ), x ≠ 0 → isNegB x = !isPosB x)
    : Array.filter isNegB nums = Array.filter (fun x => !isPosB x) nums := by
    apply Array.ext'
    rw [Array.toList_filter, Array.toList_filter]
    apply List.filter_congr
    intro x hx
    apply h_neg_is_not_pos
    obtain ⟨_, h_nonzero, _⟩ := require_1
    rw [Array.mem_toList] at hx
    obtain ⟨i, hi⟩ := Array.getElem?_of_mem hx
    simp [Array.getElem?_eq_some_iff] at hi
    obtain ⟨hi_bound, hi_eq⟩ := hi
    have h_nz := h_nonzero i hi_bound
    rw [Array.getElem!_eq_getD, Array.getD, dif_pos hi_bound] at h_nz
    rw [← hi_eq]
    exact h_nz

theorem goal_8_0_1
    (nums : Array ℤ)
    (h_filter_neg_eq : Array.filter isNegB nums = Array.filter (fun x => !isPosB x) nums)
    : (Array.filter isPosB nums ++ Array.filter isNegB nums).Perm nums := by
    rw [h_filter_neg_eq]
    rw [Array.perm_iff_toList_perm]
    rw [Array.toList_append, Array.toList_filter, Array.toList_filter]
    exact List.filter_append_perm isPosB nums.toList

theorem goal_8_0_2
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (res : Array ℤ)
    (invariant_res_size : res.size = nums.size)
    (i_6 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (invariant_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (done_1 : nums.size ≤ i_1)
    (invariant_neg_eq_filter : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_pos_eq_filter : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_j_bound : nums.size ≤ nums.size)
    (invariant_odd_filled : ∀ k < nums.size, k % OfNat.ofNat 2 = OfNat.ofNat 1 → res[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)
    (invariant_even_filled : ∀ k < nums.size, k % OfNat.ofNat 2 = OfNat.ofNat 0 → res[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!)
    (done_2 : nums.size ≤ nums.size)
    (snd_eq : (nums.size + OfNat.ofNat 1) / OfNat.ofNat 2 = i_6 ∧ res = res)
    (h_even_filled : ∀ k < nums.size, k % 2 = 0 → res[k]! = (Array.filter isPosB nums)[k / 2]!)
    (h_odd_filled : ∀ k < nums.size, k % 2 = 1 → res[k]! = (Array.filter isNegB nums)[k / 2]!)
    (h_neg_is_not_pos : ∀ (x : ℤ), x ≠ 0 → isNegB x = !isPosB x)
    (h_filter_neg_eq : Array.filter isNegB nums = Array.filter (fun x => !isPosB x) nums)
    (h_concat_perm : (Array.filter isPosB nums ++ Array.filter isNegB nums).Perm nums)
    : res.Perm (Array.filter isPosB nums ++ Array.filter isNegB nums) := by
    sorry


theorem goal_8_0
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (res : Array ℤ)
    (invariant_res_size : res.size = nums.size)
    (i_6 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (invariant_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (done_1 : nums.size ≤ i_1)
    (invariant_neg_eq_filter : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_pos_eq_filter : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_j_bound : nums.size ≤ nums.size)
    (invariant_odd_filled : ∀ k < nums.size, k % OfNat.ofNat 2 = OfNat.ofNat 1 → res[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)
    (invariant_even_filled : ∀ k < nums.size, k % OfNat.ofNat 2 = OfNat.ofNat 0 → res[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!)
    (done_2 : nums.size ≤ nums.size)
    (snd_eq : (nums.size + OfNat.ofNat 1) / OfNat.ofNat 2 = i_6 ∧ res = res)
    (h_even_filled : ∀ k < nums.size, k % 2 = 0 → res[k]! = (Array.filter isPosB nums)[k / 2]!)
    (h_odd_filled : ∀ k < nums.size, k % 2 = 1 → res[k]! = (Array.filter isNegB nums)[k / 2]!)
    : res.Perm nums := by
    have h_neg_is_not_pos : ∀ x : ℤ, x ≠ 0 → (isNegB x = !isPosB x) := by expose_names; intros; expose_names; try simp_all; try grind
    have h_filter_neg_eq : Array.filter isNegB nums = Array.filter (fun x => !isPosB x) nums := by expose_names; exact (goal_8_0_0 nums require_1 h_neg_is_not_pos)
    have h_concat_perm : (Array.filter isPosB nums ++ Array.filter isNegB nums).Perm nums := by expose_names; exact (goal_8_0_1 nums h_filter_neg_eq)
    have h_res_perm_concat : res.Perm (Array.filter isPosB nums ++ Array.filter isNegB nums) := by expose_names; exact (goal_8_0_2 nums require_1 i_1 res invariant_res_size i_6 invariant_i_bound invariant_neg_size invariant_pos_size done_1 invariant_neg_eq_filter invariant_pos_eq_filter invariant_j_bound invariant_odd_filled invariant_even_filled done_2 snd_eq h_even_filled h_odd_filled h_neg_is_not_pos h_filter_neg_eq h_concat_perm)
    exact h_res_perm_concat.trans h_concat_perm

theorem goal_8_1
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧
  (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧
    Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (res : Array ℤ)
    (invariant_res_size : res.size = nums.size)
    (i_6 : ℕ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (invariant_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (done_1 : nums.size ≤ i_1)
    (invariant_neg_eq_filter : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_pos_eq_filter : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_j_bound : nums.size ≤ nums.size)
    (invariant_odd_filled : ∀ k < nums.size, k % OfNat.ofNat 2 = OfNat.ofNat 1 → res[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)
    (invariant_even_filled : ∀ k < nums.size, k % OfNat.ofNat 2 = OfNat.ofNat 0 → res[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!)
    (done_2 : nums.size ≤ nums.size)
    (snd_eq : (nums.size + OfNat.ofNat 1) / OfNat.ofNat 2 = i_6 ∧ res = res)
    (h_even_filled : ∀ k < nums.size, k % 2 = 0 → res[k]! = (Array.filter isPosB nums)[k / 2]!)
    (h_odd_filled : ∀ k < nums.size, k % 2 = 1 → res[k]! = (Array.filter isNegB nums)[k / 2]!)
    : stableBySign nums res := by
    sorry



theorem goal_8
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (res : Array ℤ)
    (invariant_res_size : res.size = nums.size)
    (i_4 : ℕ)
    (i_6 : ℕ)
    (res_1 : Array ℤ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (invariant_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_j_bound : i_4 ≤ nums.size)
    (invariant_odd_filled : ∀ k < i_4, k % OfNat.ofNat 2 = OfNat.ofNat 1 → res[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)
    (invariant_even_filled : ∀ k < i_4, k % OfNat.ofNat 2 = OfNat.ofNat 0 → res[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!)
    (done_1 : nums.size ≤ i_1)
    (invariant_neg_eq_filter : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_pos_eq_filter : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    (snd_eq : (i_4 + OfNat.ofNat 1) / OfNat.ofNat 2 = i_6 ∧ res = res_1)
    : postcondition nums res_1 := by
    have h_eq : res = res_1 := snd_eq.2
    have h_j_eq : i_4 = nums.size := Nat.le_antisymm invariant_j_bound done_2
    subst h_eq
    subst h_j_eq
    have h_even_filled : ∀ k < nums.size, k % 2 = 0 → res[k]! = (Array.filter isPosB nums)[k / 2]! := invariant_even_filled
    have h_odd_filled : ∀ k < nums.size, k % 2 = 1 → res[k]! = (Array.filter isNegB nums)[k / 2]! := invariant_odd_filled
    unfold postcondition
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- 1. res.size = nums.size
    · exact invariant_res_size
    -- 2. res.Perm nums
    · have h_perm : res.Perm nums := by expose_names; exact (goal_8_0 nums require_1 i_1 res invariant_res_size i_6 invariant_i_bound invariant_neg_size invariant_pos_size done_1 invariant_neg_eq_filter invariant_pos_eq_filter invariant_j_bound invariant_odd_filled invariant_even_filled done_2 snd_eq h_even_filled h_odd_filled)
      exact h_perm
    -- 3. alternatesStartingPos res
    · have h_alt : alternatesStartingPos res := by expose_names; intros; expose_names; try simp_all; try grind
      exact h_alt
    -- 4. res.size > 0 → res[0]! > 0
    · have h_first_pos : res.size > 0 → res[0]! > 0 := by expose_names; intros; expose_names; try simp_all; try grind
      exact h_first_pos
    -- 5. stableBySign nums res
    · have h_stable : stableBySign nums res := by expose_names; exact (goal_8_1 nums require_1 i_1 res invariant_res_size i_6 invariant_i_bound invariant_neg_size invariant_pos_size done_1 invariant_neg_eq_filter invariant_pos_eq_filter invariant_j_bound invariant_odd_filled invariant_even_filled done_2 snd_eq h_even_filled h_odd_filled)
      exact h_stable



theorem goal_8
    (nums : Array ℤ)
    (require_1 : nums.size % OfNat.ofNat 2 = OfNat.ofNat 0 ∧ (∀ i < nums.size, ¬nums[i]! = OfNat.ofNat 0) ∧ Array.countP isPosB nums = nums.size / OfNat.ofNat 2 ∧ Array.countP isNegB nums = nums.size / OfNat.ofNat 2)
    (i_1 : ℕ)
    (res : Array ℤ)
    (invariant_res_size : res.size = nums.size)
    (i_4 : ℕ)
    (i_6 : ℕ)
    (res_1 : Array ℤ)
    (invariant_i_bound : i_1 ≤ nums.size)
    (invariant_neg_size : (Array.filter isNegB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_pos_size : (Array.filter isPosB nums).size = nums.size / OfNat.ofNat 2)
    (invariant_j_bound : i_4 ≤ nums.size)
    (invariant_odd_filled : ∀ k < i_4, k % OfNat.ofNat 2 = OfNat.ofNat 1 → res[k]! = (Array.filter isNegB nums)[k / OfNat.ofNat 2]!)
    (invariant_even_filled : ∀ k < i_4, k % OfNat.ofNat 2 = OfNat.ofNat 0 → res[k]! = (Array.filter isPosB nums)[k / OfNat.ofNat 2]!)
    (done_1 : nums.size ≤ i_1)
    (invariant_neg_eq_filter : Array.filter isNegB nums = Array.filter isNegB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (invariant_pos_eq_filter : Array.filter isPosB nums = Array.filter isPosB (nums.extract (OfNat.ofNat 0) i_1) (OfNat.ofNat 0) (min i_1 nums.size))
    (done_2 : nums.size ≤ i_4)
    (snd_eq : (i_4 + OfNat.ofNat 1) / OfNat.ofNat 2 = i_6 ∧ res = res_1)
    : postcondition nums res_1 := by
    sorry



prove_correct RearrangeArrayElementsBySign by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i invariant_i_bound if_pos if_pos_1)
  exact (goal_1 nums require_1 i if_pos if_pos_1)
  exact (goal_2 nums i if_pos if_neg)
  exact (goal_3 nums require_1 i invariant_i_bound if_pos if_neg)
  exact (goal_4 nums i_1 invariant_i_bound done_1)
  exact (goal_5 nums i_1 invariant_i_bound done_1)
  exact (goal_6 nums require_1 i_1 invariant_i_bound done_1)
  exact (goal_7 nums require_1 i_1 invariant_i_bound done_1)
  exact (goal_8 nums require_1 i_1 res invariant_res_size i_4 i_6 res_1 invariant_i_bound invariant_neg_size invariant_pos_size invariant_j_bound invariant_odd_filled invariant_even_filled done_1 invariant_neg_eq_filter invariant_pos_eq_filter done_2 snd_eq)
end Proof
