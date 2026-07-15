/- This file type checks in Lean 4.28 -/

import Mathlib

set_option maxHeartbeats 10000000

-- Compatibility alias: mkArray was renamed to Array.replicate in newer Lean
def mkArray := @Array.replicate

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

section ArrayHelpers

/-
PROVIDED SOLUTION
Unfold getElem! to get a dite. Use Array.size_set! to simplify the size condition, then unfold set! to set with the bound proof, and use Array.getElem_set with the inequality h to show the element is unchanged.
-/
lemma array_set_getElem_ne (a : Array ℤ) (i j : Nat) (v : ℤ) (hi : i < a.size) (hj : j < a.size) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  cases a ; aesop

/-
PROVIDED SOLUTION
Unfold getElem! to get a dite. Use Array.size_set! to simplify the size condition, then unfold set! to set with the bound proof, and use Array.getElem_set to get the value v.
-/
lemma array_set_getElem_eq (a : Array ℤ) (i : Nat) (v : ℤ) (hi : i < a.size) :
    (a.set! i v)[i]! = v := by
  cases a ; aesop

end ArrayHelpers

section Proof

/-
PROBLEM
Helper: strict increasing prefix is preserved after appending a larger element via set!

PROVIDED SOLUTION
For i + 1 < k + 1, we have two cases:

Case 1: i + 1 < k. Then both i < k and i + 1 < k, so both are ≠ k. Use array_set_getElem_ne (with k ≠ i and k ≠ i+1 since i < k and i+1 ≤ k-1 < k or i+1 = k-1) to get (out.set! k v)[i]! = out[i]! and (out.set! k v)[i+1]! = out[i+1]!. Then apply h_strict.

Case 2: i + 1 = k, i.e. i = k - 1. Then (out.set! k v)[i]! = (out.set! k v)[k-1]! = out[k-1]! (by array_set_getElem_ne since k-1 ≠ k when k ≥ 1). And (out.set! k v)[i+1]! = (out.set! k v)[k]! = v (by array_set_getElem_eq). So we need out[k-1]! < v, which is h_last_lt.
-/
lemma strict_after_set (out : Array ℤ) (k : Nat) (v : ℤ)
    (h_one_le : 1 ≤ k) (h_k_lt_size : k < out.size)
    (h_strict : ∀ i, i + 1 < k → out[i]! < out[i + 1]!)
    (h_last_lt : out[k - 1]! < v) :
    ∀ i, i + 1 < k + 1 → (out.set! k v)[i]! < (out.set! k v)[i + 1]! := by
  intros i hi;
  by_cases hi' : i + 1 = k;
  · cases out ; aesop;
  · rw [ array_set_getElem_ne, array_set_getElem_ne ] <;> norm_num [ h_k_lt_size, h_one_le, h_last_lt ];
    · exact h_strict i ( lt_of_le_of_ne ( Nat.le_of_lt_succ hi ) hi' );
    · linarith;
    · tauto;
    · omega;
    · omega

/-
PROBLEM
The original lemma `dedup_step` is false as stated: it is missing a hypothesis
that k < out.size (equivalently, k ≤ m + 1). Counterexample: nums = #[1,2],
m = 0, k = 2, out = #[0,1] satisfies all hypotheses but the conclusion requires
3 ≤ 2 in the not-equal branch.
The corrected version below adds `h_k_lt_size : k < out.size`.

Original (commented out because it is false):
lemma dedup_step (nums : Array ℤ) (h_sorted : ArraySortedLe nums) (m k : Nat) (out : Array ℤ)
    (hm : m + 1 < nums.size) (h_size : out.size = nums.size) (h_one_le : 1 ≤ k)
    (h_k_le_size : k ≤ out.size) (h_strict : ∀ i, i + 1 < k → out[i]! < out[i + 1]!)
    (h_last : out[k - 1]! = nums[m]!) :
    let res := if (nums[m + 1]! != nums[m + 1 - 1]!) = true
                 then (k + 1, out.set! k nums[m + 1]!)
                 else (k, out)
    res.2.size = nums.size ∧
    1 ≤ res.1 ∧
    res.1 ≤ res.2.size ∧
    (∀ i, i + 1 < res.1 → res.2[i]! < res.2[i + 1]!) ∧
    res.2[res.1 - 1]! = nums[m + 1]! := by
  sorry

Corrected version of `dedup_step` with the added hypothesis `k < out.size`.

PROVIDED SOLUTION
Simplify m + 1 - 1 to m. Split on whether nums[m+1]! = nums[m]!.

EQUAL CASE: bne is false, res = (k, out). All parts follow from hypotheses directly. Last element: out[k-1]! = nums[m]! = nums[m+1]!.

NOT-EQUAL CASE: bne is true, res = (k+1, out.set! k nums[m+1]!).
1. Size: Array.size_set! preserves size, so h_size.
2. 1 ≤ k+1: omega.
3. k+1 ≤ out.size: Since k < out.size (h_k_lt_size) and size preserved by set!, k+1 ≤ out.size.
4. Strict increasing: Apply strict_after_set with h_one_le, h_k_lt_size, h_strict, and out[k-1]! < nums[m+1]! (which follows from h_last: out[k-1]! = nums[m]!, and nums[m]! < nums[m+1]! since they're sorted and not equal).
5. Last element: (k+1)-1 = k, and (out.set! k nums[m+1]!)[k]! = nums[m+1]! by array_set_getElem_eq.

Key: use array_set_getElem_eq for item 5, and strict_after_set for item 4.
-/
lemma dedup_step (nums : Array ℤ) (h_sorted : ArraySortedLe nums) (m k : Nat) (out : Array ℤ)
    (hm : m + 1 < nums.size) (h_size : out.size = nums.size) (h_one_le : 1 ≤ k)
    (h_k_lt_size : k < out.size) (h_strict : ∀ i, i + 1 < k → out[i]! < out[i + 1]!)
    (h_last : out[k - 1]! = nums[m]!) :
    let res := if (nums[m + 1]! != nums[m + 1 - 1]!) = true
                 then (k + 1, out.set! k nums[m + 1]!)
                 else (k, out)
    res.2.size = nums.size ∧
    1 ≤ res.1 ∧
    res.1 ≤ res.2.size ∧
    (∀ i, i + 1 < res.1 → res.2[i]! < res.2[i + 1]!) ∧
    res.2[res.1 - 1]! = nums[m + 1]! := by
  split_ifs <;> simp_all +decide [ Array.size_set! ];
  · intro i hi; by_cases hi' : i + 1 < k <;> simp_all +decide [ Array.setIfInBounds ] ;
    · grind;
    · have := h_sorted m hm; simp_all +decide [ Array.getElem?_eq_getElem ] ;
      grind;
  · linarith

/-
PROVIDED SOLUTION
We need to prove that after the foldl, for all x, (∃ j < n, nums[j]! = x) ↔ (∃ i < k, out[i]! = x).

Introduce the result as a let-binding, then use intro x.

For the forward direction: given j < nums.size with nums[j]! = x, we need to find i < result.1 with result.2[i]! = x. Since nums is sorted and the algorithm picks one representative for each distinct value, nums[j]! equals some nums[first_occ]! which was added to the output.

For the backward direction: given i < result.1 with result.2[i]! = x, we need j < nums.size with nums[j]! = x. Each element in the output was copied from nums, so this value exists in nums.

The proof should proceed by induction on the length of the list being folded (i.e., List.range (nums.size - 1)), maintaining the loop invariant:
- After processing indices 0..m, the output prefix contains exactly the distinct values from nums[0..m].

Actually this is quite complex. Let me suggest a different approach: prove this by establishing the loop invariant using List.foldl_induction or by unrolling the definition.

Actually, let me try to use a Nat.rec induction on nums.size. If nums.size = 1, the fold is over an empty list, so result = (1, init) where init[0]! = nums[0]!. The claim becomes: (∃ j < 1, nums[j]! = x) ↔ (∃ i < 1, init[i]! = x), which is: nums[0]! = x ↔ init[0]! = x, which is true since init[0]! = nums[0]!.

For the inductive step: processing one more element either adds it (if different from previous) or skips it (if same). In the skip case, the value was already in the prefix (by sortedness, equal to previous means already represented). In the add case, the new distinct value is added.

Try using List.foldl on List.range with strong induction.
-/
lemma foldl_dedup_membership (nums : Array ℤ) (h_sorted : ArraySortedLe nums)
    (h_pos : nums.size > 0) :
    let result := (List.range (nums.size - 1)).foldl (fun (acc : Nat × Array ℤ) idx =>
      let i := idx + 1
      if nums[i]! != nums[i - 1]! then (acc.1 + 1, acc.2.set! acc.1 nums[i]!)
      else (acc.1, acc.2)) (1, (mkArray nums.size (0 : ℤ)).set! 0 nums[0]!)
    ∀ x : ℤ, (∃ j, j < nums.size ∧ nums[j]! = x) ↔ (∃ i, i < result.1 ∧ result.2[i]! = x) := by
  intro result x;
  constructor <;> intro hx;
  · -- By induction on the number of elements processed, we can show that the result holds.
    have h_ind : ∀ (m : ℕ) (hm : m ≤ nums.size - 1), ∀ x, (∃ j < m + 1, nums[j]! = x) → (∃ i < (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
      let i := idx + 1
      if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).1, (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
      let i := idx + 1
      if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
      (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).2[i]! = x) := by
        intro m hm x hx;
        induction' m with m ih generalizing x <;> simp_all +decide [ List.range_succ ];
        · rcases nums with ⟨ ⟨ l ⟩ ⟩ <;> aesop;
        · rcases hx with ⟨ j, hj₁, hj₂ ⟩ ; rcases hj₁ with ( _ | hj₁ ) <;> simp_all +decide [ List.range_succ ] ;
          · split_ifs <;> simp_all +decide [ Array.setIfInBounds ];
            · exact ih ( Nat.le_of_lt hm ) m le_rfl;
            · have h_ind : (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
                let i := idx + 1
                if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
                (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).1 < (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
                let i := idx + 1
                if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
                (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).2.size := by
                  have h_ind : ∀ (m : ℕ) (hm : m ≤ nums.size - 1), (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
                    let i := idx + 1
                    if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
                    (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).1 ≤ m + 1 ∧ (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
                    let i := idx + 1
                    if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
                    (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).2.size = nums.size := by
                      intro m hm; induction' m with m ih <;> simp_all +decide [ List.range_succ ] ;
                      · simp +decide [ mkArray ];
                      · grind;
                  grind;
              use (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
                let i := idx + 1
                if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
                (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range m)).1;
              grind;
          · obtain ⟨ i, hi, hi' ⟩ := ih ( Nat.le_of_lt hm ) j hj₁;
            use i;
            grind;
    exact h_ind _ le_rfl _ ⟨ hx.choose, Nat.lt_succ_of_le ( Nat.le_sub_one_of_lt hx.choose_spec.1 ), hx.choose_spec.2 ⟩;
  · -- By definition of `result`, we know that every element in `result.2` is an element of `nums`.
    have h_result_subset : ∀ i < result.1, result.2[i]! ∈ nums := by
      -- By definition of `result`, we know that every element in `result.2` is an element of `nums`. We can prove this by induction on the number of elements processed.
      have h_result_subset_induction : ∀ (n : ℕ) (hn : n ≤ nums.size - 1), ∀ i < (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
        let i := idx + 1
        if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range n)).1, (List.foldl (fun (acc : ℕ × Array ℤ) (idx : ℕ) =>
        let i := idx + 1
        if (nums[i]! != nums[i - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[i]!) else (acc.1, acc.2))
        (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range n)).2[i]! ∈ nums := by
          intro n hn;
          induction' n with n ih;
          · rcases nums with ⟨ ⟨ l ⟩ ⟩ <;> aesop;
          · simp_all +decide [ List.range_succ ];
            split_ifs <;> simp_all +decide [ List.foldl ];
            · exact ih ( Nat.le_of_lt hn );
            · intro i hi;
              by_cases hi' : i < (List.foldl (fun acc idx => if nums[idx + 1]! = nums[idx]! then acc else (acc.1 + 1, acc.2.setIfInBounds acc.1 nums[idx + 1]!)) (1, (mkArray nums.size 0).setIfInBounds 0 nums[0]) (List.range n)).1;
              · grind;
              · rw [ Array.setIfInBounds ];
                split_ifs <;> simp_all +decide [ Array.set ];
                · grind;
                · have h_size : ∀ (n : ℕ) (hn : n ≤ nums.size - 1), (List.foldl (fun acc idx => if nums[idx + 1]! = nums[idx]! then acc else (acc.1 + 1, acc.2.setIfInBounds acc.1 nums[idx + 1]!)) (1, (mkArray nums.size 0).setIfInBounds 0 nums[0]) (List.range n)).2.size = nums.size := by
                    intro n hn; induction' n with n ih <;> simp_all +decide [ List.range_succ ] ;
                    · simp +decide [ mkArray ];
                    · grind;
                  have h_foldl_size : ∀ (n : ℕ) (hn : n ≤ nums.size - 1), (List.foldl (fun acc idx => if nums[idx + 1]! = nums[idx]! then acc else (acc.1 + 1, acc.2.setIfInBounds acc.1 nums[idx + 1]!)) (1, (mkArray nums.size 0).setIfInBounds 0 nums[0]) (List.range n)).1 ≤ n + 1 := by
                    intro n hn; induction' n with n ih <;> simp_all +decide [ List.range_succ ] ;
                    grind;
                  linarith [ h_size n ( Nat.le_of_lt hn ), h_foldl_size n ( Nat.le_of_lt hn ), Nat.sub_add_cancel h_pos ];
      exact h_result_subset_induction _ le_rfl;
    obtain ⟨ i, hi, hx ⟩ := hx;
    obtain ⟨ j, hj ⟩ := Array.mem_iff_getElem.mp ( h_result_subset i hi ) ; use j; aesop;

/-
PROVIDED SOLUTION
Use PrefixStrictIncreasing from h_strict to get k ≤ out.size. For the membership, convert using foldl_dedup_membership nums h_precond h_pos, and convert between x ∈ nums and ∃ j < nums.size, nums[j]! = x using Array.mem_iff_getElem.
-/
theorem correctness_goal_1_2 (nums : Array ℤ) (h_precond : precondition nums)
    (h_empty_case : nums.size = 0 → postcondition nums (implementation nums))
    (h_pos : nums.size > 0) (h_ne : ¬nums.size = 0)
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
          (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1) :
    PrefixSameMembers nums
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
  apply And.intro h_strict.left;
  convert foldl_dedup_membership nums h_precond h_pos using 1;
  rw [ Array.mem_iff_getElem ] ; aesop;

/-
PROVIDED SOLUTION
Define f(i) = Nat.find (the first index j in nums such that nums[j]! = out[i]!). This exists because h_members says every value in the prefix appears in nums.

Show: (1) f(i) < nums.size and out[i]! = nums[f(i)]! - by definition of Nat.find applied to PrefixSameMembers.
(2) f is strictly increasing: if i < j then out[i]! < out[j]! (from h_strict, PrefixStrictIncreasing). Since nums is sorted (h_precond) and f(i) is first occurrence of out[i]!, f(j) is first occurrence of out[j]!, and out[i]! < out[j]!, we must have f(i) < f(j) because if f(j) ≤ f(i) then by sortedness nums[f(j)]! ≤ nums[f(i)]! i.e. out[j]! ≤ out[i]!, contradicting out[i]! < out[j]!.
(3) First occurrence: for j < f(i), nums[j]! ≠ out[i]! by minimality of Nat.find.

The key is constructing f using classical choice (Nat.find) and using the sorted property of nums together with the strict increasing property of the prefix.
-/
theorem correctness_goal_1_3 (nums : Array ℤ) (h_precond : precondition nums)
    (h_empty_case : nums.size = 0 → postcondition nums (implementation nums))
    (h_pos : nums.size > 0) (h_ne : ¬nums.size = 0)
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
          (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2) :
    PrefixOccursInOrderFirst nums
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
  -- Define the function f that maps to the first occurrence of each value in the prefix.
  have h_f : ∀ i < (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).1, ∃ j < nums.size, nums[j]! = (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2[i]! ∧ ∀ k < j, nums[k]! ≠ (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2[i]! := by
    intro i hi
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j < nums.size, nums[j]! = (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2[i]! := by
      have := h_members.2 ( ( List.foldl ( fun acc idx => if ( nums[idx + 1]! != nums[idx + 1 - 1]! ) = true then ( acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]! ) else ( acc.1, acc.2 ) ) ( 1, ( mkArray nums.size 0 ).set! 0 nums[0]! ) ( List.range ( nums.size - 1 ) ) ).2[i]! );
      have := Array.mem_iff_getElem.mp ( this.mpr ⟨ i, hi, rfl ⟩ ) ; aesop;
    use Nat.find (⟨j, hj₁, hj₂⟩ : ∃ j < nums.size, nums[j]! = (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2[i]!);
    exact ⟨ Nat.find_spec ( ⟨ j, hj₁, hj₂ ⟩ : ∃ j < nums.size, nums[j]! = _ ) |>.1, Nat.find_spec ( ⟨ j, hj₁, hj₂ ⟩ : ∃ j < nums.size, nums[j]! = _ ) |>.2, fun k hk => fun hk' => Nat.find_min ( ⟨ j, hj₁, hj₂ ⟩ : ∃ j < nums.size, nums[j]! = _ ) hk ⟨ by linarith [ Nat.find_spec ( ⟨ j, hj₁, hj₂ ⟩ : ∃ j < nums.size, nums[j]! = _ ) |>.1 ], hk' ⟩ ⟩;
  choose! f hf using h_f;
  refine' ⟨ f, _, _, _ ⟩;
  · exact fun i hi => ⟨ hf i hi |>.1, hf i hi |>.2.1.symm ⟩;
  · intros i j hij hj_lt_k
    have h_lt : (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2[i]! < (List.foldl (fun acc idx => if (nums[idx + 1]! != nums[idx + 1 - 1]!) = true then (acc.1 + 1, acc.2.set! acc.1 nums[idx + 1]!) else (acc.1, acc.2)) (1, (mkArray nums.size 0).set! 0 nums[0]!) (List.range (nums.size - 1))).2[j]! := by
      have := h_strict.2 i;
      induction' hij with k hk ih;
      · exact this hj_lt_k;
      · exact lt_trans ( ih ( Nat.lt_of_succ_lt hj_lt_k ) ) ( h_strict.2 _ ( by linarith ) );
    have h_lt : ∀ k l : ℕ, k < l → l < nums.size → nums[k]! ≤ nums[l]! := by
      intros k l hkl hl_lt_size
      induction' hkl with k l hkl ih;
      · exact h_precond k hl_lt_size;
      · exact le_trans ( hkl ( Nat.lt_of_succ_lt hl_lt_size ) ) ( h_precond _ ( by linarith ) );
    grind +ring;
  · exact fun i hi j hj => hf i hi |>.2.2 j hj

end Proof
