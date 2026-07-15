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
def mergeHelper (nums1 : Array Int) (nums2 : Array Int) (i j : Nat) (acc : Array Int) : Array Int :=
  if hi : i < nums1.size then
    if hj : j < nums2.size then
      if nums1[i] ≤ nums2[j] then
        mergeHelper nums1 nums2 (i + 1) j (acc.push nums1[i])
      else
        mergeHelper nums1 nums2 i (j + 1) (acc.push nums2[j])
    else
      -- nums2 exhausted, append rest of nums1
      if i < nums1.size then
        let acc' := nums1.toList.drop i |>.foldl (fun a x => a.push x) acc
        acc'
      else acc
  else
    -- nums1 exhausted, append rest of nums2
    if j < nums2.size then
      let acc' := nums2.toList.drop j |>.foldl (fun a x => a.push x) acc
      acc'
    else acc
termination_by (nums1.size - i) + (nums2.size - j)

def implementation (nums1 : Array Int) (nums2 : Array Int) : Array Int :=
  mergeHelper nums1 nums2 0 0 (Array.mkEmpty (nums1.size + nums2.size))
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
#assert_same_evaluation #[(implementation test1_nums1 test1_nums2), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums1 test2_nums2), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums1 test3_nums2), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums1 test4_nums2), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums1 test5_nums2), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums1 test6_nums2), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums1 test7_nums2), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums1 test8_nums2), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums1 test9_nums2), test9_Expected]
end Assertions

section Pbt
method implementationPbt (nums1 : Array Int) (nums2 : Array Int)
  return (result : Array Int)
  require precondition nums1 nums2
  ensures postcondition nums1 nums2 result
  do
  return (implementation nums1 nums2)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
-- Helper: foldl push produces acc ++ l.toArray
private lemma foldl_push_eq (l : List ℤ) (acc : Array ℤ) :
    l.foldl (fun a x => a.push x) acc = acc ++ l.toArray := by
  exact List.foldl_push

private lemma foldl_push_size (l : List ℤ) (acc : Array ℤ) :
    (l.foldl (fun a x => a.push x) acc).size = acc.size + l.length := by
  rw [foldl_push_eq]
  simp [Array.size_append, List.size_toArray]

private lemma foldl_push_countInArray (l : List ℤ) (acc : Array ℤ) (v : ℤ) :
    countInArray (l.foldl (fun a x => a.push x) acc) v = countInArray acc v + l.count v := by
  unfold countInArray
  rw [foldl_push_eq]
  simp [Array.toList_append, List.count_append, List.count_toArray]

private lemma foldl_push_toList (l : List ℤ) (acc : Array ℤ) :
    (l.foldl (fun a x => a.push x) acc).toList = acc.toList ++ l := by
  rw [foldl_push_eq]
  simp [Array.toList_append]

private lemma sortedNondecreasing_push (acc : Array ℤ) (x : ℤ)
    (h_sorted : sortedNondecreasing acc)
    (h_last : acc.size = 0 ∨ acc[acc.size - 1]! ≤ x) :
    sortedNondecreasing (acc.push x) := by
  unfold sortedNondecreasing at *
  intro i hi
  rw [Array.size_push] at hi
  have hi_lt : i < acc.size := by omega
  by_cases heq : i + 1 < acc.size
  · -- Both i and i+1 in acc
    rw [getElem!_pos (acc.push x) i (by rw [Array.size_push]; omega),
        getElem!_pos (acc.push x) (i+1) (by rw [Array.size_push]; omega),
        Array.getElem_push_lt hi_lt,
        Array.getElem_push_lt heq]
    have := h_sorted i heq
    rw [getElem!_pos acc i hi_lt, getElem!_pos acc (i+1) heq] at this
    exact this
  · -- i+1 = acc.size, so i = acc.size - 1
    have h_eq : i + 1 = acc.size := by omega
    rw [getElem!_pos (acc.push x) i (by rw [Array.size_push]; omega),
        getElem!_pos (acc.push x) (i+1) (by rw [Array.size_push]; omega)]
    rw [Array.getElem_push_lt hi_lt]
    have h_not : ¬(i + 1 < acc.size) := by omega
    rw [Array.getElem_push (by rw [Array.size_push]; omega), dif_neg h_not]
    cases h_last with
    | inl h0 => omega
    | inr hle =>
      rw [getElem!_pos acc (acc.size - 1) (by omega)] at hle
      have : i = acc.size - 1 := by omega
      subst this
      exact hle

private lemma sortedNondecreasing_concat_list (acc : Array ℤ) (l : List ℤ)
    (h_acc_sorted : sortedNondecreasing acc)
    (h_l_sorted : ∀ (k : ℕ), k + 1 < l.length → l[k]! ≤ l[k + 1]!)
    (h_bridge : acc.size = 0 ∨ (l ≠ [] → acc[acc.size - 1]! ≤ l[0]!)) :
    sortedNondecreasing (acc ++ l.toArray) := by
  unfold sortedNondecreasing at *
  intro i hi
  have h_sz : (acc ++ l.toArray).size = acc.size + l.length := by
    simp [Array.size_append, List.size_toArray]
  rw [h_sz] at hi
  have h_isz : i < (acc ++ l.toArray).size := by rw [h_sz]; omega
  have h_i1sz : i + 1 < (acc ++ l.toArray).size := by rw [h_sz]; omega
  rw [getElem!_pos _ i h_isz, getElem!_pos _ (i+1) h_i1sz]
  by_cases h1 : i + 1 < acc.size
  · have h0 : i < acc.size := by omega
    rw [Array.getElem_append_left h0, Array.getElem_append_left h1]
    have := h_acc_sorted i h1
    rw [getElem!_pos _ i h0, getElem!_pos _ (i+1) h1] at this
    exact this
  · by_cases h2 : i < acc.size
    · have h_ieq : i = acc.size - 1 := by omega
      rw [Array.getElem_append_left h2]
      rw [Array.getElem_append_right (show acc.size ≤ i + 1 by omega)]
      simp only [List.getElem_toArray, show i + 1 - acc.size = 0 from by omega]
      cases h_bridge with
      | inl h0 => omega
      | inr hbr =>
        have h_ne : l ≠ [] := by intro h; subst h; simp at hi; omega
        have hb := hbr h_ne
        rw [getElem!_pos acc (acc.size - 1) (by omega), getElem!_pos l 0 (by omega)] at hb
        convert hb using 2
    · rw [Array.getElem_append_right (show acc.size ≤ i by omega),
          Array.getElem_append_right (show acc.size ≤ i + 1 by omega)]
      simp only [List.getElem_toArray]
      have := h_l_sorted (i - acc.size) (by omega)
      rw [getElem!_pos l (i - acc.size) (by omega),
          getElem!_pos l (i - acc.size + 1) (by omega)] at this
      convert this using 2
      omega

private lemma sorted_drop_list (arr : Array ℤ) (j : ℕ) (h : sortedNondecreasing arr) (hj : j ≤ arr.size) :
    ∀ (k : ℕ), k + 1 < (arr.toList.drop j).length → (arr.toList.drop j)[k]! ≤ (arr.toList.drop j)[k + 1]! := by
  intro k hk
  rw [List.length_drop, Array.length_toList] at hk
  rw [getElem!_pos _ k (by rw [List.length_drop, Array.length_toList]; omega),
      getElem!_pos _ (k + 1) (by rw [List.length_drop, Array.length_toList]; omega)]
  rw [List.getElem_drop, List.getElem_drop]
  have h1 : j + k < arr.size := by omega
  have h2 : j + (k + 1) < arr.size := by omega
  rw [show arr.toList[j + k] = arr[j + k] from Array.getElem_toList h1,
      show arr.toList[j + (k + 1)] = arr[j + (k + 1)] from Array.getElem_toList h2]
  unfold sortedNondecreasing at h
  have := h (j + k) (by omega)
  rw [getElem!_pos arr (j + k) h1, getElem!_pos arr (j + k + 1) (by omega)] at this
  convert this using 2

private lemma drop_head_eq_toList_getElem (arr : Array ℤ) (j : ℕ) (hj : j < arr.size) :
    (arr.toList.drop j)[0]! = arr.toList[j]! := by
  have h1 : 0 < (arr.toList.drop j).length := by rw [List.length_drop, Array.length_toList]; omega
  have h2 : j < arr.toList.length := by rw [Array.length_toList]; exact hj
  rw [getElem!_pos _ 0 h1, getElem!_pos _ j h2]
  rw [List.getElem_drop]
  simp

private lemma sorted_foldl_drop (arr : Array ℤ) (acc : Array ℤ) (j : ℕ)
    (h_arr_sorted : sortedNondecreasing arr)
    (h_acc_sorted : sortedNondecreasing acc)
    (hj : j ≤ arr.size)
    (h_bridge : acc.size = 0 ∨ (j < arr.size → acc[acc.size - 1]! ≤ arr.toList[j]!)) :
    sortedNondecreasing (List.foldl (fun a x => a.push x) acc (arr.toList.drop j)) := by
  rw [foldl_push_eq]
  apply sortedNondecreasing_concat_list acc (arr.toList.drop j) h_acc_sorted
  · exact sorted_drop_list arr j h_arr_sorted hj
  · cases h_bridge with
    | inl h0 => left; exact h0
    | inr hbr =>
      right
      intro hne
      have h_len : 0 < (arr.toList.drop j).length := by
        cases h : arr.toList.drop j with
        | nil => exact absurd h hne
        | cons _ _ => simp
      have hj' : j < arr.size := by
        rw [List.length_drop, Array.length_toList] at h_len; omega
      rw [drop_head_eq_toList_getElem arr j hj']
      exact hbr hj'


theorem correctness_goal_0_0
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (h_precond : precondition nums1 nums2)
    (n1 : Array ℤ)
    (n2 : Array ℤ)
    : ∀ (fuel i j : ℕ) (acc : Array ℤ),
  n1.size - i + (n2.size - j) ≤ fuel →
    sortedNondecreasing n1 →
      sortedNondecreasing n2 →
        i ≤ n1.size →
          j ≤ n2.size →
            sortedNondecreasing acc →
              acc.size = 0 ∨
                  (i < n1.size → acc[acc.size - 1]! ≤ n1.toList[i]!) ∧
                    (j < n2.size → acc[acc.size - 1]! ≤ n2.toList[j]!) →
                (mergeHelper n1 n2 i j acc).size = acc.size + (n1.size - i) + (n2.size - j) ∧
                  sortedNondecreasing (mergeHelper n1 n2 i j acc) ∧
                    ∀ (v : ℤ),
                      countInArray (mergeHelper n1 n2 i j acc) v =
                        countInArray acc v + List.count v (List.drop i n1.toList) + List.count v (List.drop j n2.toList) := by
    sorry


theorem correctness_goal_0
    (nums1 : Array ℤ)
    (nums2 : Array ℤ)
    (h_precond : precondition nums1 nums2)
    : ∀ (nums1 nums2 : Array ℤ) (i j : ℕ) (acc : Array ℤ),
  sortedNondecreasing nums1 →
    sortedNondecreasing nums2 →
      i ≤ nums1.size →
        j ≤ nums2.size →
          sortedNondecreasing acc →
            acc.size = 0 ∨
                (i < nums1.size → acc[acc.size - 1]! ≤ nums1.toList[i]!) ∧
                  (j < nums2.size → acc[acc.size - 1]! ≤ nums2.toList[j]!) →
              (mergeHelper nums1 nums2 i j acc).size = acc.size + (nums1.size - i) + (nums2.size - j) ∧
                sortedNondecreasing (mergeHelper nums1 nums2 i j acc) ∧
                  ∀ (v : ℤ),
                    countInArray (mergeHelper nums1 nums2 i j acc) v =
                      countInArray acc v + List.count v (List.drop i nums1.toList) +
                        List.count v (List.drop j nums2.toList) := by
    intro n1 n2
    -- We do strong induction on the measure (n1.size - i) + (n2.size - j)
    have main : ∀ (fuel : ℕ), ∀ (i j : ℕ) (acc : Array ℤ),
      (n1.size - i) + (n2.size - j) ≤ fuel →
      sortedNondecreasing n1 →
      sortedNondecreasing n2 →
      i ≤ n1.size →
      j ≤ n2.size →
      sortedNondecreasing acc →
      acc.size = 0 ∨
          (i < n1.size → acc[acc.size - 1]! ≤ n1.toList[i]!) ∧
            (j < n2.size → acc[acc.size - 1]! ≤ n2.toList[j]!) →
      (mergeHelper n1 n2 i j acc).size = acc.size + (n1.size - i) + (n2.size - j) ∧
        sortedNondecreasing (mergeHelper n1 n2 i j acc) ∧
          ∀ (v : ℤ),
            countInArray (mergeHelper n1 n2 i j acc) v =
              countInArray acc v + List.count v (List.drop i n1.toList) +
                List.count v (List.drop j n2.toList) := by expose_names; exact (correctness_goal_0_0 nums1 nums2 h_precond n1 n2)
    intro i j acc hs1 hs2 hi hj hacc hstitch
    exact main ((n1.size - i) + (n2.size - j)) i j acc (Nat.le_refl _) hs1 hs2 hi hj hacc hstitch


theorem correctness_goal
    (nums1 : Array Int)
    (nums2 : Array Int)
    (h_precond : precondition nums1 nums2)
    : postcondition nums1 nums2 (implementation nums1 nums2) := by
    have h_inv : ∀ (nums1 nums2 : Array Int) (i j : Nat) (acc : Array Int),
      sortedNondecreasing nums1 → sortedNondecreasing nums2 →
      i ≤ nums1.size → j ≤ nums2.size →
      sortedNondecreasing acc →
      (acc.size = 0 ∨ (i < nums1.size → acc[acc.size - 1]! ≤ nums1.toList[i]!) ∧
                       (j < nums2.size → acc[acc.size - 1]! ≤ nums2.toList[j]!)) →
      (mergeHelper nums1 nums2 i j acc).size = acc.size + (nums1.size - i) + (nums2.size - j) ∧
      sortedNondecreasing (mergeHelper nums1 nums2 i j acc) ∧
      (∀ v : Int, countInArray (mergeHelper nums1 nums2 i j acc) v = countInArray acc v +
        (nums1.toList.drop i).count v + (nums2.toList.drop j).count v) := by expose_names; exact (correctness_goal_0 nums1 nums2 h_precond)
    unfold postcondition implementation
    have h_mkEmpty : Array.mkEmpty (nums1.size + nums2.size) = (#[] : Array Int) := Array.mkEmpty_eq
    rw [h_mkEmpty]
    have h_empty_sorted : sortedNondecreasing (#[] : Array Int) := by
      unfold sortedNondecreasing; intro i hi; simp [Array.size_empty] at hi
    have h_result := h_inv nums1 nums2 0 0 #[] h_precond.1 h_precond.2
      (Nat.zero_le _) (Nat.zero_le _) h_empty_sorted (Or.inl Array.size_empty)
    simp [Array.size_empty, List.drop] at h_result
    obtain ⟨h_size, h_sort, h_count⟩ := h_result
    refine ⟨?_, h_sort, ?_⟩
    · omega
    · intro v
      unfold countInArray at h_count ⊢
      have := h_count v
      simp [countInArray, Array.size_empty] at this ⊢
      omega
end Proof
