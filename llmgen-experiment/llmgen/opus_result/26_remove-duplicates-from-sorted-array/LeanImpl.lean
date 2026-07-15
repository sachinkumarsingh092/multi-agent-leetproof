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
def postcondition (nums : Array Int) (result : Nat × Array Int) : Prop :=
  result.snd.size = nums.size ∧
    PrefixStrictIncreasing result.snd result.fst ∧
    PrefixSameMembers nums result.fst result.snd ∧
    PrefixOccursInOrderFirst nums result.snd result.fst
end Specs

section Impl
def implementation (nums : Array Int) : Nat × Array Int :=
  if nums.size = 0 then (0, nums)
  else
    let n := nums.size
    -- Initialize output array with zeros of same size
    let out := mkArray n (0 : Int)
    -- Place first element
    let out := out.set! 0 nums[0]!
    -- Use a fold over indices 1..n-1 to process remaining elements
    let (k, out) := (List.range (n - 1)).foldl (fun (acc : Nat × Array Int) idx =>
      let i := idx + 1
      let (k, out) := acc
      if nums[i]! != nums[i - 1]! then
        (k + 1, out.set! k nums[i]!)
      else
        (k, out)
    ) (1, out)
    (k, out)
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
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Pbt
method implementationPbt (nums : Array Int)
  return (result : Nat × Array Int)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    : nums.size = 0 → postcondition nums (implementation nums) := by
    intro hsz
    have heq : nums = #[] := Array.eq_empty_of_size_eq_zero hsz
    subst heq
    simp [implementation, postcondition, PrefixStrictIncreasing, PrefixSameMembers, PrefixOccursInOrderFirst, Array.not_mem_empty]

theorem correctness_goal_1_0
    (nums : Array ℤ)
    : (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2.size =
  nums.size := by
    have hmk : (mkArray nums.size (0 : ℤ)).size = nums.size := by
      exact Array.size_replicate
    suffices h : ∀ (l : List ℕ) (acc : ℕ × Array ℤ),
      acc.2.size = nums.size →
      (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        acc l).2.size = nums.size by
      apply h
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hmk]
    intro l
    induction l with
    | nil => intro acc hacc; simpa using hacc
    | cons hd tl ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      split
      · simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hacc]
      · exact hacc

private lemma list_foldl_range_induction {β : Type*} (P : Nat → β → Prop)
    (f : β → Nat → β) (init : β) (n : Nat)
    (h0 : P 0 init)
    (hstep : ∀ m b, m < n → P m b → P (m + 1) (f b m))
    : P n ((List.range n).foldl f init) := by
  induction n with
  | zero => simpa [List.range]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    apply hstep k _ (by omega)
    exact ih (fun m b hm hP => hstep m b (by omega) hP)

private lemma dedup_step
    (nums : Array ℤ) (h_sorted : ArraySortedLe nums)
    (m k : Nat) (out : Array ℤ)
    (hm : m + 1 < nums.size)
    (h_size : out.size = nums.size)
    (h_one_le : 1 ≤ k)
    (h_k_le_size : k ≤ out.size)
    (h_strict : ∀ i, i + 1 < k → out[i]! < out[i + 1]!)
    (h_last : out[k - 1]! = nums[m]!)
    : let res := if (nums[m + 1]! != nums[m + 1 - 1]!) = true 
                 then (k + 1, out.set! k nums[m + 1]!)
                 else (k, out)
      res.2.size = nums.size ∧
      1 ≤ res.1 ∧
      res.1 ≤ res.2.size ∧
      (∀ i, i + 1 < res.1 → res.2[i]! < res.2[i + 1]!) ∧
      res.2[res.1 - 1]! = nums[m + 1]! := by
  simp only
  have hm1_minus : m + 1 - 1 = m := by omega
  rw [hm1_minus]
  by_cases heq : nums[m + 1]! = nums[m]!
  · -- Equal case
    have hbne_false : (nums[m + 1]! != nums[m]!) = false := by simp [bne, heq]
    rw [hbne_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨h_size, h_one_le, h_k_le_size, h_strict, by rw [h_last, heq]⟩
  · -- Different case
    have hbne_true : (nums[m + 1]! != nums[m]!) = true := by simp [bne, heq]
    rw [hbne_true]
    simp only [↓reduceIte]
    have h_le : nums[m]! ≤ nums[m + 1]! := h_sorted m (by omega)
    have h_lt_vals : nums[m]! < nums[m + 1]! := lt_of_le_of_ne h_le (fun h => heq h.symm)
    -- We need k < out.size. We have k ≤ out.size. But is k < out.size?
    -- Actually, we need to add k ≤ m + 1 to the invariant for this.
    -- For now, from h_k_le_size : k ≤ out.size and h_size : out.size = nums.size
    -- We don't necessarily have k < out.size from the current hypotheses alone...
    -- Actually we need a stronger invariant. Let me add k ≤ m + 1 which gives k < nums.size
    sorry

private lemma setIfInBounds_getElem!_ne {out : Array ℤ} {k : Nat} {v : ℤ} {j : Nat}
    (hne : k ≠ j) :
    (out.setIfInBounds k v)[j]! = out[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD]
  have hsz : (out.setIfInBounds k v).size = out.size := Array.size_setIfInBounds
  by_cases hj : j < out.size
  · have hj' : j < (out.setIfInBounds k v).size := by rw [hsz]; exact hj
    simp [hj, hj']
    rw [show (out.setIfInBounds k v)[j] = if k = j then v else out[j] from
        Array.getElem_setIfInBounds hj]
    simp [hne]
  · have hj' : ¬(j < (out.setIfInBounds k v).size) := by rw [hsz]; exact hj
    simp [hj, hj']

private lemma setIfInBounds_getElem!_self {out : Array ℤ} {k : Nat} {v : ℤ}
    (hk : k < out.size) :
    (out.setIfInBounds k v)[k]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD]
  have hk' : k < (out.setIfInBounds k v).size := by 
    rw [Array.size_setIfInBounds]; exact hk
  rw [dif_pos hk']
  exact Array.getElem_setIfInBounds_self hk'

private lemma dedup_step2
    (nums : Array ℤ) (h_sorted : ArraySortedLe nums)
    (m k : Nat) (out : Array ℤ)
    (hm : m + 1 < nums.size)
    (h_size : out.size = nums.size)
    (h_one_le : 1 ≤ k)
    (h_k_bound : k ≤ m + 1)
    (h_strict : ∀ i, i + 1 < k → out[i]! < out[i + 1]!)
    (h_last : out[k - 1]! = nums[m]!)
    : let res := if (nums[m + 1]! != nums[m + 1 - 1]!) = true 
                 then (k + 1, out.set! k nums[m + 1]!)
                 else (k, out)
      res.2.size = nums.size ∧
      1 ≤ res.1 ∧
      res.1 ≤ m + 1 + 1 ∧
      (∀ i, i + 1 < res.1 → res.2[i]! < res.2[i + 1]!) ∧
      res.2[res.1 - 1]! = nums[m + 1]! := by
  simp only
  have hm1_minus : m + 1 - 1 = m := by omega
  rw [hm1_minus]
  have hk_lt_size : k < nums.size := by omega
  have hk_lt_out : k < out.size := by omega
  by_cases heq : nums[m + 1]! = nums[m]!
  · -- Equal case
    have hbne_false : (nums[m + 1]! != nums[m]!) = false := by simp [bne, heq]
    rw [hbne_false]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨h_size, h_one_le, by omega, h_strict, by rw [h_last, heq]⟩
  · -- Different case
    have hbne_true : (nums[m + 1]! != nums[m]!) = true := by simp [bne, heq]
    rw [hbne_true]; simp only [↓reduceIte]
    have h_le : nums[m]! ≤ nums[m + 1]! := h_sorted m (by omega)
    have h_lt_vals : nums[m]! < nums[m + 1]! := lt_of_le_of_ne h_le (fun h => heq h.symm)
    have h_size' : (out.set! k nums[m + 1]!).size = nums.size := by
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, h_size]
    refine ⟨h_size', by omega, by omega, ?_, ?_⟩
    · -- Strict increasing for k+1
      intro i hi
      rw [Array.set!_eq_setIfInBounds]
      by_cases hik : i + 1 = k
      · -- Boundary: i = k-1
        have hi_eq : i = k - 1 := by omega
        subst hi_eq
        have : k - 1 + 1 = k := by omega
        rw [this]
        rw [setIfInBounds_getElem!_ne (by omega : k ≠ k - 1)]
        rw [setIfInBounds_getElem!_self hk_lt_out]
        rw [h_last]
        exact h_lt_vals
      · -- Interior: i + 1 < k
        have hi1_lt_k : i + 1 < k := by omega
        rw [setIfInBounds_getElem!_ne (by omega : k ≠ i)]
        rw [setIfInBounds_getElem!_ne (by omega : k ≠ i + 1)]
        exact h_strict i hi1_lt_k
    · -- Last element
      rw [Array.set!_eq_setIfInBounds]
      have : k + 1 - 1 = k := by omega
      rw [this]
      exact setIfInBounds_getElem!_self hk_lt_out

private lemma mkArray_size_eq (n : Nat) (v : ℤ) : (mkArray n v).size = n := by
  simp [mkArray]

private lemma foldl_dedup_invariant
    (nums : Array ℤ)
    (h_sorted : ArraySortedLe nums)
    (h_pos : nums.size > 0)
    : let f := fun (acc : Nat × Array ℤ) (idx : Nat) =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2)
      let init : Nat × Array ℤ := (1, (mkArray nums.size (0 : ℤ)).set! 0 nums[0]!)
      let res := (List.range (nums.size - 1)).foldl f init
      res.2.size = nums.size ∧
      1 ≤ res.1 ∧
      res.1 ≤ nums.size ∧
      (∀ (i : Nat), i + 1 < res.1 → res.2[i]! < res.2[i + 1]!) := by
  intro f init
  let P : Nat → (Nat × Array ℤ) → Prop := fun m acc =>
    acc.2.size = nums.size ∧
    1 ≤ acc.1 ∧
    acc.1 ≤ m + 1 ∧
    (∀ (i : Nat), i + 1 < acc.1 → acc.2[i]! < acc.2[i + 1]!) ∧
    acc.2[acc.1 - 1]! = nums[m]!
  suffices h_inv : P (nums.size - 1) ((List.range (nums.size - 1)).foldl f init) by
    obtain ⟨h1, h2, h3, h4, _⟩ := h_inv
    exact ⟨h1, h2, by omega, h4⟩
  apply list_foldl_range_induction P f init (nums.size - 1)
  · -- Base case: P 0 init
    show init.2.size = nums.size ∧ 1 ≤ init.1 ∧ init.1 ≤ 0 + 1 ∧
      (∀ i, i + 1 < init.1 → init.2[i]! < init.2[i + 1]!) ∧ init.2[init.1 - 1]! = nums[0]!
    have h_init2_size : init.2.size = nums.size := by
      show ((mkArray nums.size (0 : ℤ)).set! 0 nums[0]!).size = nums.size
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, mkArray_size_eq]
    have h_init2_0 : init.2[init.1 - 1]! = nums[0]! := by
      show ((mkArray nums.size (0 : ℤ)).set! 0 nums[0]!)[1 - 1]! = nums[0]!
      simp only [Nat.sub_self]
      rw [Array.set!_eq_setIfInBounds]
      exact setIfInBounds_getElem!_self (by rw [mkArray_size_eq]; omega)
    refine ⟨h_init2_size, ?_, ?_, ?_, h_init2_0⟩
    · show 1 ≤ 1; omega
    · show 1 ≤ 0 + 1; omega
    · show ∀ i, i + 1 < 1 → _
      intro i hi; omega
  · -- Inductive step
    intro m ⟨k, out⟩ hm ⟨h_size, h_one_le, h_k_bound, h_strict, h_last⟩
    exact dedup_step2 nums h_sorted m k out (by omega) h_size h_one_le h_k_bound h_strict h_last


theorem correctness_goal_1_1
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h_pos : nums.size > 0)
    : PrefixStrictIncreasing
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1 := by
  unfold PrefixStrictIncreasing
  have h_inv := foldl_dedup_invariant nums h_precond h_pos
  obtain ⟨h1, h2, h3, h4⟩ := h_inv
  exact ⟨by rw [h1]; exact h3, h4⟩

private lemma getElem!_setIfInBounds_eq {xs : Array ℤ} {i : Nat} {v : ℤ} (h : i < xs.size) :
    (xs.setIfInBounds i v)[i]! = v := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self, h]

private lemma getElem!_setIfInBounds_ne {xs : Array ℤ} {i j : Nat} {v : ℤ} (h : i ≠ j) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

private lemma sorted_le_trans (nums : Array ℤ) (h_sorted : ArraySortedLe nums) (i j : Nat) (hij : i ≤ j) (hj : j < nums.size) : nums[i]! ≤ nums[j]! := by
  induction hij with
  | refl => exact le_refl _
  | @step k hik ih =>
    have : nums[i]! ≤ nums[k]! := ih (by omega)
    have : nums[k]! ≤ nums[k + 1]! := h_sorted k (by omega)
    linarith

private lemma mem_iff_exists_index (nums : Array ℤ) (x : ℤ) :
    x ∈ nums ↔ ∃ j, j < nums.size ∧ nums[j]! = x := by
  rw [Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, ?_⟩
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rw [show nums[i]? = some (nums[i]'hi) from Array.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩]
    simpa
  · rintro ⟨j, hj, heq⟩
    refine ⟨j, hj, ?_⟩
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at heq
    rw [show nums[j]? = some (nums[j]'hj) from Array.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩] at heq
    simpa using heq

private lemma foldl_dedup_membership (nums : Array ℤ) (h_sorted : ArraySortedLe nums) (h_pos : nums.size > 0) :
    let result := (List.range (nums.size - 1)).foldl (fun (acc : Nat × Array ℤ) idx =>
      let i := idx + 1
      if nums[i]! != nums[i - 1]! then (acc.1 + 1, acc.2.set! acc.1 nums[i]!)
      else (acc.1, acc.2)) (1, (mkArray nums.size (0 : ℤ)).set! 0 nums[0]!)
    ∀ x : ℤ, (∃ j, j < nums.size ∧ nums[j]! = x) ↔ (∃ i, i < result.1 ∧ result.2[i]! = x) := by
  -- Use list_foldl_range_induction with predicate P m (k, out) :=
  --   out.size = nums.size ∧ 1 ≤ k ∧ k ≤ m + 1 ∧ k ≤ out.size ∧
  --   out[k-1]! = nums[m]! ∧
  --   ∀ x, (∃ j, j ≤ m ∧ j < nums.size ∧ nums[j]! = x) ↔ (∃ i, i < k ∧ out[i]! = x)
  let n := nums.size
  let f := fun (acc : Nat × Array ℤ) (idx : Nat) =>
    let i := idx + 1
    if nums[i]! != nums[i - 1]! then (acc.1 + 1, acc.2.set! acc.1 nums[i]!)
    else (acc.1, acc.2)
  let init : Nat × Array ℤ := (1, (mkArray n (0 : ℤ)).set! 0 nums[0]!)
  let P := fun (m : Nat) (acc : Nat × Array ℤ) =>
    acc.2.size = n ∧
    1 ≤ acc.1 ∧ acc.1 ≤ m + 1 ∧ acc.1 ≤ acc.2.size ∧
    acc.2[acc.1 - 1]! = nums[m]! ∧
    (∀ x : ℤ, (∃ j, j ≤ m ∧ j < n ∧ nums[j]! = x) ↔ (∃ i, i < acc.1 ∧ acc.2[i]! = x))
  have hfinal := list_foldl_range_induction P f init (n - 1)
  sorry


theorem correctness_goal_1_2
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h_empty_case : nums.size = 0 → postcondition nums (implementation nums))
    (h_pos : nums.size > 0)
    (h_ne : ¬nums.size = 0)
    (h_size_out : (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2.size =
  nums.size)
    (h_strict : PrefixStrictIncreasing
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1)
    : PrefixSameMembers nums
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2 := by
    sorry

theorem correctness_goal_1_3
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h_empty_case : nums.size = 0 → postcondition nums (implementation nums))
    (h_pos : nums.size > 0)
    (h_ne : ¬nums.size = 0)
    (h_size_out : (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2.size =
  nums.size)
    (h_strict : PrefixStrictIncreasing
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1)
    (h_members : PrefixSameMembers nums
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2)
    : PrefixOccursInOrderFirst nums
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2
  (List.foldl
      (fun acc idx =>
        if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
        else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1 := by
    sorry


theorem correctness_goal_1
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h_empty_case : nums.size = 0 → postcondition nums (implementation nums))
    : nums.size > 0 → postcondition nums (implementation nums) := by
    intro h_pos
    have h_ne : ¬ (nums.size = 0) := by omega
    -- The key: establish a big invariant about the fold result
    -- The fold processes indices 0..n-2 (via List.range (n-1))
    -- We need: the result satisfies the postcondition
    -- Let's establish the four parts of the postcondition separately
    -- but all referencing the same concrete expression
    have h_size_out : (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2.size = nums.size := by expose_names; exact (correctness_goal_1_0 nums)
    have h_strict : PrefixStrictIncreasing (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2 (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1 := by expose_names; exact (correctness_goal_1_1 nums h_precond h_pos)
    have h_members : PrefixSameMembers nums (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1 (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2 := by expose_names; exact (correctness_goal_1_2 nums h_precond h_empty_case h_pos h_ne h_size_out h_strict)
    have h_order : PrefixOccursInOrderFirst nums (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2 (List.foldl
        (fun acc idx =>
          if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!)
          else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1 := by expose_names; exact (correctness_goal_1_3 nums h_precond h_empty_case h_pos h_ne h_size_out h_strict h_members)
    unfold postcondition implementation
    simp only [h_ne, ↓reduceIte]
    exact ⟨h_size_out, h_strict, h_members, h_order⟩


theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
    unfold postcondition
    have h_empty_case : nums.size = 0 → postcondition nums (implementation nums) := by expose_names; exact (correctness_goal_0 nums h_precond)
    have h_nonempty_case : nums.size > 0 → postcondition nums (implementation nums) := by expose_names; exact (correctness_goal_1 nums h_precond h_empty_case)
    unfold postcondition at h_empty_case h_nonempty_case
    by_cases h : nums.size = 0
    · exact h_empty_case h
    · exact h_nonempty_case (Nat.pos_of_ne_zero h)
end Proof
