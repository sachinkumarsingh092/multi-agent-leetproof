/- This file type checks in Lean 4.28 -/

import Lean

import Mathlib.Tactic

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

section Proof

/-
PROVIDED SOLUTION
This is a proof by strong induction on `fuel`. The key insight is that `mergeHelper` is defined recursively, decreasing `(n1.size - i) + (n2.size - j)` at each step. We case split on whether `i < n1.size` and `j < n2.size`, mirroring the structure of `mergeHelper`. In each recursive case, we unfold `mergeHelper` once using `mergeHelper.eq_def` or `simp only [mergeHelper]`, then apply the inductive hypothesis with fuel-1. The base cases are when both indices are exhausted. For the recursive cases, we need to show the accumulator invariants are maintained after pushing an element.
-/
theorem correctness_goal_0_0 (nums1 : Array ℤ) (nums2 : Array ℤ) (h_precond : precondition nums1 nums2) (n1 : Array ℤ) (n2 : Array ℤ) : ∀ (fuel i j : ℕ) (acc : Array ℤ),
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
    intros fuel i j acc hfuel h_n1 h_n2 hi hj h_acc h_acc_size
    induction' fuel with fuel ih generalizing i j acc <;> simp_all +decide [ Nat.sub_add_comm ];
    · unfold mergeHelper;
      grind +ring;
    · unfold mergeHelper; simp_all +decide [ Nat.sub_add_comm ] ;
      split_ifs <;> simp_all +decide [ Nat.sub_add_comm ];
      · specialize ih ( i + 1 ) j ( acc.push n1[i] ) ; simp_all +decide [ Nat.sub_add_comm ] ;
        convert ih ( by omega ) _ _ using 1;
        · rw [ show n1.size - i = n1.size - ( i + 1 ) + 1 by omega ] ; ring;
        · unfold countInArray; simp +decide [ List.drop ] ; ring;
          rw [ show List.drop i n1.toList = n1[i] :: List.drop ( i + 1 ) n1.toList from ?_ ] ; simp +decide [ List.count_cons ] ; ring;
          · exact fun _ => forall_congr' fun _ => by ring;
          · rw [ List.drop_eq_getElem_cons ] ; aesop;
        · intro k hk; rcases h_acc_size with ( rfl | h_acc_size ) <;> simp_all +decide [ Array.push ] ;
          by_cases hk' : k < acc.size - 1 <;> simp_all +decide [ List.getElem?_append ];
          · convert h_acc k ( by omega ) using 1;
            · exact?;
            · grind;
          · grind +ring;
        · exact fun h => h_n1 i h |> le_trans ( by aesop ) |> le_trans <| by aesop;
      · specialize ih i ( j + 1 ) ( acc.push n2[j] ) ; simp_all +decide [ Nat.sub_add_comm ] ;
        convert ih ( by omega ) _ ( by linarith ) _ using 1;
        · rw [ show n2.size - j = ( n2.size - ( j + 1 ) ) + 1 by omega ] ; ring;
        · simp +decide [ countInArray, List.drop ];
          rw [ show List.drop j n2.toList = n2[j] :: List.drop ( j + 1 ) n2.toList from ?_ ];
          · simp +decide [ add_comm, add_left_comm, add_assoc, List.count_cons ];
          · rw [ List.drop_eq_getElem_cons ] ; aesop;
        · intro k hk; rcases lt_trichotomy k ( acc.size - 1 ) with ( hk' | rfl | hk' ) <;> simp_all +decide [ Nat.sub_add_cancel ] ;
          · convert h_acc k ( by omega ) using 1;
            · grind +ring;
            · grind +ring;
          · grind +ring;
          · omega;
        · intro h; specialize h_n2 j; aesop;
      · constructor;
        · intro k hk; rcases lt_trichotomy k acc.size with hk' | rfl | hk' <;> simp_all +decide [ List.getElem?_append ] ;
          · by_cases hk'' : k + 1 < acc.size <;> simp_all +decide [ Array.getElem_append ];
            · convert h_acc k hk'' using 1;
              · grind;
              · exact?;
            · grind;
          · convert h_n1 i ( by omega ) using 1;
            · grind;
            · grind;
          · have h_pos : (acc ++ (List.drop i n1.toList).toArray)[k]! = n1[i + (k - acc.size)]! ∧ (acc ++ (List.drop i n1.toList).toArray)[k + 1]! = n1[i + (k - acc.size) + 1]! := by
              grind +ring;
            convert h_n1 ( i + ( k - acc.size ) ) _ using 1;
            · exact h_pos.left;
            · grind;
            · omega;
        · simp_all +decide [ countInArray ];
          rw [ List.drop_eq_nil_of_le ] <;> aesop;
      · -- Since `acc` is sorted and `n2.toList.drop j` is sorted, their concatenation is also sorted.
        have h_sorted : sortedNondecreasing (acc ++ (List.drop j n2.toList).toArray) := by
          intro k hk; by_cases hk' : k < acc.size <;> simp_all +decide [ Nat.add_mod, Nat.mod_eq_of_lt ] ;
          · by_cases hk'' : k + 1 < acc.size <;> simp_all +decide [ Array.getElem_append ];
            · convert h_acc k hk'' using 1;
              · grind;
              · exact?;
            · grind;
          · -- Since `acc` is sorted and `n2` is sorted, the element at position `k` in the concatenated array is the element at position `k - acc.size` in `n2`.
            have h_element : (acc ++ (List.drop j n2.toList).toArray)[k]! = n2[j + (k - acc.size)]! := by
              grind +ring
            generalize_proofs at *; (
            rw [ h_element ] ; specialize h_n2 ( j + ( k - acc.size ) ) ; simp_all +decide [ Nat.sub_add_comm ( by linarith : acc.size ≤ k ) ] ;
            grind)
        generalize_proofs at *; (
        simp_all +decide [ countInArray, List.count_append ];
        grind);
      · simp_all +decide [ le_antisymm hi ‹_›, le_antisymm hj ‹_› ];
        simp +decide [ List.drop_eq_nil_of_le ]

end Proof
