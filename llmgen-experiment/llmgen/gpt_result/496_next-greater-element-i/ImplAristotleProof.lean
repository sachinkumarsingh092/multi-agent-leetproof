import Mathlib

-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    496. Next Greater Element I: For each element of nums1, find its next greater element in nums2.
    **Important: complexity should be O(m + n) time and O(n) space**
    Natural language breakdown:
    1. We are given two 0-indexed arrays nums1 and nums2 of integers.
    2. All elements in each array are distinct.
    3. Every element of nums1 appears somewhere in nums2 (nums1 is a subset of nums2).
    4. For a value x located at index j in nums2, its next greater element is the first element strictly greater than x that occurs at some index k > j.
    5. If such a k exists, the answer for x is nums2[k].
    6. If no such k exists, the answer for x is -1.
    7. The returned array ans has the same length as nums1.
    8. For each i, ans[i] is determined by the position of nums1[i] within nums2 and the next-greater rule above.
-/

section Specs
-- Helper predicates are written purely in terms of Array operations (no Array/List conversion).

def DistinctArray (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < a.size → j < a.size → i ≠ j → a[i]! ≠ a[j]!

def IsSubsetArray (small : Array Int) (big : Array Int) : Prop :=
  ∀ (i : Nat), i < small.size → ∃ (j : Nat), j < big.size ∧ big[j]! = small[i]!

-- x occurs in array a at index j.
def OccursAt (a : Array Int) (x : Int) (j : Nat) : Prop :=
  j < a.size ∧ a[j]! = x

-- k is the (index of the) next greater element for position j in a.
-- This means:
-- * it is to the right (j < k)
-- * it is strictly greater
-- * no earlier index between j and k is strictly greater (k is the first such index)
def NextGreaterIndex (a : Array Int) (j : Nat) (k : Nat) : Prop :=
  j < k ∧
  k < a.size ∧
  a[k]! > a[j]! ∧
  (∀ (t : Nat), j < t → t < k → a[t]! ≤ a[j]!)

def HasNextGreater (a : Array Int) (j : Nat) : Prop :=
  ∃ (k : Nat), NextGreaterIndex a j k

-- v is the next-greater value for index j; v = -1 iff no next-greater exists.
def NextGreaterValue (a : Array Int) (j : Nat) (v : Int) : Prop :=
  (v = (-1) ∧ ¬ HasNextGreater a j) ∨
  (∃ (k : Nat), NextGreaterIndex a j k ∧ v = a[k]!)

-- Preconditions

def precondition (nums1 : Array Int) (nums2 : Array Int) : Prop :=
  DistinctArray nums1 ∧
  DistinctArray nums2 ∧
  IsSubsetArray nums1 nums2

-- Postconditions

def postcondition (nums1 : Array Int) (nums2 : Array Int) (ans : Array Int) : Prop :=
  ans.size = nums1.size ∧
  (∀ (i : Nat), i < nums1.size →
    ∃ (j : Nat), OccursAt nums2 nums1[i]! j ∧ NextGreaterValue nums2 j ans[i]!)
end Specs

section TestCases
-- Test case 1: Example 1
-- nums1 = [4,1,2], nums2 = [1,3,4,2] => [-1,3,-1]
def test1_nums1 : Array Int := #[4, 1, 2]
def test1_nums2 : Array Int := #[1, 3, 4, 2]
def test1_Expected : Array Int := #[-1, 3, -1]

-- Test case 2: Example 2
-- nums1 = [2,4], nums2 = [1,2,3,4] => [3,-1]
def test2_nums1 : Array Int := #[2, 4]
def test2_nums2 : Array Int := #[1, 2, 3, 4]
def test2_Expected : Array Int := #[3, -1]

-- Test case 3: nums1 empty (vacuous subset), nums2 non-empty
-- ans should be empty
def test3_nums1 : Array Int := #[]
def test3_nums2 : Array Int := #[5, 1, 7]
def test3_Expected : Array Int := #[]

-- Test case 4: both arrays empty
def test4_nums1 : Array Int := #[]
def test4_nums2 : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: singleton where no next greater exists
def test5_nums1 : Array Int := #[10]
def test5_nums2 : Array Int := #[10]
def test5_Expected : Array Int := #[-1]

-- Test case 6: singleton where next greater exists immediately
def test6_nums1 : Array Int := #[1]
def test6_nums2 : Array Int := #[1, 2]
def test6_Expected : Array Int := #[2]

-- Test case 7: includes negative values
-- nums2 = [-2, -1, -3, 0], next greater of -2 is -1, of -3 is 0
def test7_nums1 : Array Int := #[-2, -3]
def test7_nums2 : Array Int := #[-2, -1, -3, 0]
def test7_Expected : Array Int := #[-1, 0]

-- Test case 8: nums1 = nums2, mixed next-greater and -1
def test8_nums1 : Array Int := #[3, 1, 4, 2]
def test8_nums2 : Array Int := #[3, 1, 4, 2]
def test8_Expected : Array Int := #[4, 4, -1, -1]

-- Test case 9: next greater is not adjacent (must be the first greater to the right)
-- nums2 = [2,1,3]; next greater of 1 is 3
def test9_nums1 : Array Int := #[1]
def test9_nums2 : Array Int := #[2, 1, 3]
def test9_Expected : Array Int := #[3]

-- Recommend to validate: parsing, precondition satisfiable, postcondition captures “first greater to the right”
end TestCases

section Proof

/-
PROVIDED SOLUTION
By invariant_final_partition_all, for any j < nums2.size, either (1) ∃ u < mp_1.size with mp_1[u].1 = nums2[j], or (2) ∃ p < stack_1.size with stack_1[p] = j. In case (1), u < mp_1.size < mp_1.size + 1, and (mp_1.push ...)[u] = mp_1[u], so the first disjunct holds for the extended array. In case (2), the second disjunct is preserved unchanged. Use Array.getElem!_push_lt for accessing elements at indices < mp_1.size in the pushed array.
-/
theorem goal_4 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (mp_1 : Array (ℤ × ℤ)) (s : ℕ) (invariant_final_s_bound : s ≤ stack_1.size) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < mp_1.size, mp_1[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_final_stack_prefix_mapped : ∀ p < s, ∃ u < mp_1.size, mp_1[u]!.1 = nums2[stack_1[p]!]! ∧ mp_1[u]!.2 = -OfNat.ofNat 1) (if_pos : s < stack_1.size) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_mp_sound : ∀ t < mp_1.size, ∃ j, (j < nums2.size ∧ nums2[j]! = mp_1[t]!.1) ∧ ((mp_1[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ mp_1[t]!.2 = nums2[k]!)) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) : ∀ j < nums2.size, (∃ u < mp_1.size + OfNat.ofNat 1, (mp_1.push (nums2[stack_1[s]!]!, -OfNat.ofNat 1))[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j := by
  -- Apply the hypothesis `invariant_final_partition_all` to the new mp_1.
  intros j hj
  specialize invariant_final_partition_all j hj;
  -- By definition of `push`, we can split into the two cases from `invariant_final_partition_all`.
  cases' invariant_final_partition_all with h_case1 h_case2;
  · -- Since added_mp_1 is just mp_1 with an additional element at the end, if u is less than mp_1.size, then in added_mp_1, the element at position u would still be mp_1[u]!.1. So, the first part of the disjunction should hold.
    obtain ⟨u, hu₁, hu₂⟩ := h_case1;
    use Or.inl ⟨u, by
      exact Nat.lt_succ_of_lt hu₁, by
      grind +ring⟩;
  · exact Or.inr h_case2

/-
PROVIDED SOLUTION
For t < mp_1.size + 1: Case t < mp_1.size: By invariant_final_mp_sound, ∃ j with the needed properties for mp_1[t]. Since (mp_1.push x)[t] = mp_1[t] when t < mp_1.size (Array.getElem!_push_lt), the same j works. Case t = mp_1.size: The pushed element is (nums2[stack_1[s]!]!, -1). Take j = stack_1[s]!. Then j < nums2.size by invariant_nge_stack_lt_i. (mp_1.push ...)[mp_1.size] has .1 = nums2[stack_1[s]!]! and .2 = -1. Choose the left disjunct (-1 branch). The condition ∀ x, j < x → x < nums2.size → nums2[j] < nums2[x] → ∃ x_1... is vacuously true because invariant_final_stack_no_greater_suffix (with p = s) says all t > stack_1[s]! with t < nums2.size have nums2[t] ≤ nums2[stack_1[s]!], so no x satisfies nums2[j] < nums2[x].
-/
theorem goal_5 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (mp_1 : Array (ℤ × ℤ)) (s : ℕ) (invariant_final_s_bound : s ≤ stack_1.size) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < mp_1.size, mp_1[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_final_stack_prefix_mapped : ∀ p < s, ∃ u < mp_1.size, mp_1[u]!.1 = nums2[stack_1[p]!]! ∧ mp_1[u]!.2 = -OfNat.ofNat 1) (if_pos : s < stack_1.size) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_mp_sound : ∀ t < mp_1.size, ∃ j, (j < nums2.size ∧ nums2[j]! = mp_1[t]!.1) ∧ ((mp_1[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ mp_1[t]!.2 = nums2[k]!)) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) : ∀ t < mp_1.size + OfNat.ofNat 1, ∃ j, (j < nums2.size ∧ nums2[j]! = (mp_1.push (nums2[stack_1[s]!]!, -OfNat.ofNat 1))[t]!.1) ∧ (((mp_1.push (nums2[stack_1[s]!]!, -OfNat.ofNat 1))[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ (mp_1.push (nums2[stack_1[s]!]!, -OfNat.ofNat 1))[t]!.2 = nums2[k]!) := by
  intro t ht; by_cases h : t < mp_1.size <;> simp_all +decide [ Array.getElem_push ] ;
  cases h.eq_or_lt <;> first | linarith | aesop

/-
PROVIDED SOLUTION
For p < s + 1: Case p < s: By invariant_final_stack_prefix_mapped, ∃ u < mp_1.size with mp_1[u].1 = nums2[stack_1[p]!] and mp_1[u].2 = -1. Since u < mp_1.size < mp_1.size + 1, and (mp_1.push x)[u] = mp_1[u] (Array.getElem!_push_lt), the same u works. Case p = s: Take u = mp_1.size. Then u < mp_1.size + 1. (mp_1.push (nums2[stack_1[s]!]!, -1))[mp_1.size] = (nums2[stack_1[s]!]!, -1), so .1 = nums2[stack_1[s]!]! = nums2[stack_1[p]!]! and .2 = -1.
-/
theorem goal_6 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (mp_1 : Array (ℤ × ℤ)) (s : ℕ) (invariant_final_s_bound : s ≤ stack_1.size) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < mp_1.size, mp_1[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_final_stack_prefix_mapped : ∀ p < s, ∃ u < mp_1.size, mp_1[u]!.1 = nums2[stack_1[p]!]! ∧ mp_1[u]!.2 = -OfNat.ofNat 1) (if_pos : s < stack_1.size) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_mp_sound : ∀ t < mp_1.size, ∃ j, (j < nums2.size ∧ nums2[j]! = mp_1[t]!.1) ∧ ((mp_1[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ mp_1[t]!.2 = nums2[k]!)) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) : ∀ p < s + OfNat.ofNat 1, ∃ u < mp_1.size + OfNat.ofNat 1, (mp_1.push (nums2[stack_1[s]!]!, -OfNat.ofNat 1))[u]!.1 = nums2[stack_1[p]!]! ∧ (mp_1.push (nums2[stack_1[s]!]!, -OfNat.ofNat 1))[u]!.2 = -OfNat.ofNat 1 := by
  intro p hp;
  by_cases hp' : p < s;
  · obtain ⟨ u, hu, hu' ⟩ := invariant_final_stack_prefix_mapped p hp';
    use u;
    grind;
  · use mp_1.size;
    simp +decide [ show p = s by linarith ]

/-
PROVIDED SOLUTION
Given j < nums2.size, since done_1 says nums2.size ≤ i_1, we have j < i_1. Apply invariant_nge_scanned_partition to get the result.
-/
theorem goal_7 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_1 : ℕ) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (invariant_nge_i_bound : i_1 ≤ nums2.size) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < i_1) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < i_1 → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < i_1, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (done_1 : nums2.size ≤ i_1) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j := by
  exact fun j hj => invariant_nge_scanned_partition j ( by linarith )

/-
PROVIDED SOLUTION
Since if_pos: a < nums1.size and require_1.2.2: ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!, there exists j0 < nums2.size with nums2[j0] = nums1[a]. By invariant_final_partition_all, j0 is either in i_4 (∃ u < i_4.size, i_4[u].1 = nums2[j0] = nums1[a], done) or on the stack (∃ p < stack_1.size, stack_1[p] = j0). In the stack case, since done_3: stack_1.size ≤ s_1, we have p < s_1. By invariant_final_stack_prefix_mapped, ∃ u < i_4.size with i_4[u].1 = nums2[stack_1[p]!] = nums2[j0] = nums1[a].
-/
theorem goal_8 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (i_4 : Array (ℤ × ℤ)) (s_1 : ℕ) (a : ℕ) (out : Array ℤ) (invariant_ans_a_bound : a ≤ nums1.size) (invariant_ans_out_size : out.size = nums1.size) (invariant_ans_mp_covers_nums2 : ∀ j < nums2.size, ∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) (invariant_ans_out_prefix_via_mp : ∀ k < a, ∃ u < i_4.size, i_4[u]!.1 = nums1[k]! ∧ out[k]! = i_4[u]!.2) (if_pos : a < nums1.size) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_s_bound : s_1 ≤ stack_1.size) (invariant_final_stack_prefix_mapped : ∀ p < s_1, ∃ u < i_4.size, i_4[u]!.1 = nums2[stack_1[p]!]! ∧ i_4[u]!.2 = -OfNat.ofNat 1) (invariant_ans_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) (invariant_final_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (done_3 : stack_1.size ≤ s_1) : ∃ u < i_4.size, i_4[u]!.1 = nums1[a]! := by
  obtain ⟨ j, hj, hj' ⟩ := require_1.2.2 a if_pos;
  exact hj'.symm ▸ invariant_ans_mp_covers_nums2 j hj |> fun ⟨ u, hu, hu' ⟩ => ⟨ u, hu, hu' ⟩

/-
PROVIDED SOLUTION
For k < a + 1: Case k < a: By invariant_ans_out_prefix_via_mp, ∃ u < i_4.size with i_4[u].1 = nums1[k] and out[k] = i_4[u].2. Since k < a and k ≠ a, (out.setIfInBounds a res_1)[k] = out[k] (Array.getElem!_setIfInBounds_ne or similar). So the same u works. Case k = a: By invariant_lookup_found_means_seen, ∃ u < i_4.size with i_4[u].1 = nums1[a] and res = i_4[u].2. By snd_eq, res = res_1. (out.setIfInBounds a res_1)[a] = res_1 = res = i_4[u].2 (since a < nums1.size = out.size by invariant_ans_out_size). So take this u.

Split on whether k < a or k = a (by omega from k < a + 1 and ¬(k < a)).

Case k < a: By invariant_ans_out_prefix_via_mp, get ⟨u, hu_lt, hu_eq1, hu_eq2⟩. Use this u. For the first conjunct, hu_eq1 gives i_4[u].1 = nums1[k]. For the second, we need (out.setIfInBounds a res_1)[k]! = i_4[u].2. Since k ≠ a (because k < a), and a < out.size (since a < nums1.size = out.size), setIfInBounds doesn't change index k. Use Array.getElem!_setIfInBounds to handle this - when the index k ≠ a, the value is unchanged. So (out.setIfInBounds a res_1)[k]! = out[k]! = i_4[u].2.

Case k = a: By invariant_lookup_found_means_seen, get ⟨u, hu_lt, _, hu_eq1, hu_eq2⟩ with i_4[u].1 = nums1[a] and res = i_4[u].2. By snd_eq, res = res_1. Subst k = a. Use this u. For the second conjunct: (out.setIfInBounds a res_1)[a]! = res_1 (since a < out.size = nums1.size by invariant_ans_out_size and if_pos). And res_1 = res = i_4[u].2.

Key lemmas about Array.setIfInBounds: when i < arr.size, (arr.setIfInBounds i v)[i]! = v. When j ≠ i, (arr.setIfInBounds i v)[j]! = arr[j]!. The size is preserved: (arr.setIfInBounds i v).size = arr.size.

Split on whether k < a or k = a (from k < a + 1 and ¬(k < a), get k = a by omega).

Case k < a: By invariant_ans_out_prefix_via_mp, get ⟨u, hu_lt, hu_eq1, hu_eq2⟩. We need (out.setIfInBounds a res_1)[k]! = out[k]! since k ≠ a. Use unfold of setIfInBounds (it's `if h : a < out.size then out.set a res_1 h else out`). Since a < nums1.size = out.size (by if_pos and invariant_ans_out_size), this is out.set a res_1 h. Then for getElem!, since k < out.size (because k < a < nums1.size = out.size), (out.set a res_1 h)[k]! uses the getElem! definition which reduces to (out.set a res_1 h)[k] which equals out[k] when k ≠ a. Then out[k]! = out[k] since k < out.size. So the value is preserved.

Case k = a: By invariant_lookup_found_means_seen, ∃ u < i_4.size with i_4[u].1 = nums1[a] and res = i_4[u].2. Since snd_eq gives res = res_1, we have res_1 = i_4[u].2. (out.setIfInBounds a res_1)[a]! = res_1 since a < out.size. So the result follows.

Avoid using simp_all with +decide as it's too slow. Instead use omega, have statements, and rw/simp with specific lemmas like Array.getElem_setIfInBounds, Array.size_setIfInBounds.

Unfold setIfInBounds as `if h : a < out.size then out.set a v h else out`. In the `else` case (a ≥ out.size), setIfInBounds is identity, so result is trivial. In the `if` case, (out.set a v h)[k]! = out[k]! because k ≠ a and k < out.size. Use Array.getElem_setIfInBounds which says (xs.setIfInBounds i a)[j] = if i = j then a else xs[j] when j < xs.size. Then since a ≠ k (from hk_ne), this equals out[k]. And out[k]! = out[k] since k < out.size. Similarly the LHS (out.setIfInBounds a v)[k]! = (out.setIfInBounds a v)[k] since (out.setIfInBounds a v).size = out.size and k < out.size.

Do NOT use `grind +locals` or any `grind +X` variant. Use plain `simp` or `grind`.
-/
private lemma setIfInBounds_getElem!_ne {out : Array ℤ} {a : ℕ} {v : ℤ} {k : ℕ}
    (hk_ne : k ≠ a) (hk_lt : k < out.size) :
    (out.setIfInBounds a v)[k]! = out[k]! := by
  grind

private lemma setIfInBounds_getElem!_eq {out : Array ℤ} {a : ℕ} {v : ℤ}
    (ha_lt : a < out.size) :
    (out.setIfInBounds a v)[a]! = v := by
  -- Since `a < out.size`, the else part of the if statement is taken, making the two expressions equal.
  simp [Array.setIfInBounds, ha_lt]

/-
PROVIDED SOLUTION
Split on whether k < a or k = a (from k < a + 1 and ¬(k < a), get k = a by omega).

Case k < a: By invariant_ans_out_prefix_via_mp k hk_lt, get ⟨u, hu, hu_eq1, hu_eq2⟩. Use this u. For the setIfInBounds part, since k ≠ a and k < out.size (k < a ≤ nums1.size = out.size), use setIfInBounds_getElem!_ne to rewrite (out.setIfInBounds a res_1)[k]! to out[k]!. Then out[k]! = i_4[u]!.2 from hu_eq2.

Case k = a: subst k = a. By invariant_lookup_found_means_seen, obtain ⟨u, hu_lt, _, hu_eq1, hu_eq2⟩. Use this u. For the setIfInBounds part, use setIfInBounds_getElem!_eq with a < out.size (from if_pos: a < nums1.size and invariant_ans_out_size: out.size = nums1.size). Then (out.setIfInBounds a res_1)[a]! = res_1. And by snd_eq.2, res = res_1, so res_1 = res = i_4[u]!.2 from hu_eq2.

Do NOT use grind with +ring, +revert, +suggestions, or +splitImp. Use plain grind or omega or simp.

Case split: if k < a, use invariant_ans_out_prefix_via_mp and setIfInBounds_getElem!_ne. If k ≥ a (so k = a since k < a + 1), use invariant_lookup_found_means_seen and setIfInBounds_getElem!_eq.

Key: `OfNat.ofNat 1` in the hypothesis `k < a + OfNat.ofNat 1` is just 1, so `k < a + 1` means `k ≤ a`. Combined with ¬(k < a) this gives k = a. Use `have : OfNat.ofNat 1 = 1 := rfl` or `show` to normalize. Or convert the bound using `Nat.lt_add_one_iff` or similar.

Also `snd_eq.2 : res = res_1` is needed to connect res and res_1.
-/
theorem goal_9 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (i_4 : Array (ℤ × ℤ)) (s_1 : ℕ) (a : ℕ) (out : Array ℤ) (invariant_ans_a_bound : a ≤ nums1.size) (invariant_ans_out_size : out.size = nums1.size) (invariant_ans_mp_covers_nums2 : ∀ j < nums2.size, ∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) (invariant_ans_out_prefix_via_mp : ∀ k < a, ∃ u < i_4.size, i_4[u]!.1 = nums1[k]! ∧ out[k]! = i_4[u]!.2) (if_pos : a < nums1.size) (j : ℕ) (res : ℤ) (invariant_lookup_j_bound : j ≤ i_4.size) (invariant_lookup_x_in_mp : ∃ u < i_4.size, i_4[u]!.1 = nums1[a]!) (i_7 : ℕ) (res_1 : ℤ) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_s_bound : s_1 ≤ stack_1.size) (invariant_final_stack_prefix_mapped : ∀ p < s_1, ∃ u < i_4.size, i_4[u]!.1 = nums2[stack_1[p]!]! ∧ i_4[u]!.2 = -OfNat.ofNat 1) (invariant_ans_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (snd_eq : j = i_7 ∧ res = res_1) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) (invariant_final_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (done_3 : stack_1.size ≤ s_1) (invariant_lookup_found_means_seen : ∃ u < i_4.size, u < j + OfNat.ofNat 1 ∧ i_4[u]!.1 = nums1[a]! ∧ res = i_4[u]!.2) (invariant_lookup_notfound_means_notseen : True) : ∀ k < a + OfNat.ofNat 1, ∃ u < i_4.size, i_4[u]!.1 = nums1[k]! ∧ (out.setIfInBounds a res_1)[k]! = i_4[u]!.2 := by
  intro k hk_lt;
  by_cases hk : k < a;
  · obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := invariant_ans_out_prefix_via_mp k hk;
    refine ⟨u, hu₁, hu₂, ?_⟩; rw [setIfInBounds_getElem!_ne (by linarith) (by linarith)]; exact hu₃
  · norm_num at *;
    cases hk.eq_or_lt <;> first | linarith | aesop;

/-
PROVIDED SOLUTION
For any j < nums2.size, by invariant_final_partition_all, either ∃ u < i_4.size with i_4[u].1 = nums2[j] (done), or ∃ p < stack_1.size with stack_1[p] = j. In the stack case, since done_3: stack_1.size ≤ s_1, we have p < s_1. By invariant_final_stack_prefix_mapped, ∃ u < i_4.size with i_4[u].1 = nums2[stack_1[p]!] = nums2[j].
-/
theorem goal_10 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (i_4 : Array (ℤ × ℤ)) (s_1 : ℕ) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_s_bound : s_1 ≤ stack_1.size) (invariant_final_stack_prefix_mapped : ∀ p < s_1, ∃ u < i_4.size, i_4[u]!.1 = nums2[stack_1[p]!]! ∧ i_4[u]!.2 = -OfNat.ofNat 1) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) (invariant_final_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (done_3 : stack_1.size ≤ s_1) : ∀ j < nums2.size, ∃ u < i_4.size, i_4[u]!.1 = nums2[j]! := by
  contrapose! invariant_final_mp_sound;
  obtain ⟨ j, hj₁, hj₂ ⟩ := invariant_final_mp_sound;
  obtain ⟨ p, hp₁, hp₂ ⟩ := invariant_final_partition_all j hj₁ |> Or.resolve_left <| by tauto;
  obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := invariant_final_stack_prefix_mapped p ( by linarith ) ; use u; simp_all +decide ;

/-
PROVIDED SOLUTION
Unfold postcondition. Split into two parts: (1) out_1.size = nums1.size: directly from invariant_ans_out_size. (2) For i < nums1.size: Since done_4: nums1.size ≤ i_6, we have i < i_6. By invariant_ans_out_prefix_via_mp, ∃ u < i_4.size with i_4[u].1 = nums1[i] and out_1[i] = i_4[u].2. By invariant_ans_mp_sound, ∃ j0 < nums2.size with nums2[j0] = i_4[u].1 = nums1[i] (this gives OccursAt). Also either (a) i_4[u].2 = -1 and the no-greater condition (vacuously holds because the condition says ∀ x, j0 < x → x < nums2.size → nums2[j0] < nums2[x] → ∃ x_1 between j0 and x with nums2[j0] < nums2[x_1], which means there's no next greater, so NextGreaterValue with v = -1 holds via the left disjunct), or (b) ∃ k with NextGreaterIndex properties and i_4[u].2 = nums2[k] (this gives NextGreaterValue via the right disjunct). In both cases NextGreaterValue nums2 j0 (out_1[i]) holds since out_1[i] = i_4[u].2.

For case (a), we need to show ¬HasNextGreater. HasNextGreater means ∃ k with NextGreaterIndex a j0 k, i.e., j0 < k, k < nums2.size, nums2[k] > nums2[j0], and ∀ t between j0 and k, nums2[t] ≤ nums2[j0]. But the hypothesis says for any x with j0 < x < nums2.size and nums2[j0] < nums2[x], there exists x_1 with j0 < x_1 < x and nums2[j0] < nums2[x_1]. Taking x = k (the smallest such), we get x_1 between j0 and k with nums2[j0] < nums2[x_1], contradicting ∀ t between j0 and k, nums2[t] ≤ nums2[j0]. So no such k exists.

Unfold postcondition, NextGreaterValue, NextGreaterIndex, OccursAt, HasNextGreater as needed.
-/
theorem goal_11 (nums1 : Array ℤ) (nums2 : Array ℤ) (require_1 : (∀ (i j : ℕ), i < nums1.size → j < nums1.size → ¬i = j → ¬nums1[i]! = nums1[j]!) ∧ (∀ (i j : ℕ), i < nums2.size → j < nums2.size → ¬i = j → ¬nums2[i]! = nums2[j]!) ∧ ∀ i < nums1.size, ∃ j < nums2.size, nums2[j]! = nums1[i]!) (i_2 : Array (ℤ × ℤ)) (stack_1 : Array ℕ) (invariant_final_stack_no_greater_suffix : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (i_4 : Array (ℤ × ℤ)) (s_1 : ℕ) (invariant_ans_mp_covers_nums2 : ∀ j < nums2.size, ∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) (i_6 : ℕ) (out_1 : Array ℤ) (invariant_nge_stack_increasing : ∀ (p q : ℕ), p < q → q < stack_1.size → stack_1[p]! < stack_1[q]!) (invariant_nge_stack_lt_i : ∀ p < stack_1.size, stack_1[p]! < nums2.size) (invariant_nge_stack_no_greater_between : ∀ p < stack_1.size, ∀ (t : ℕ), stack_1[p]! < t → t < nums2.size → nums2[t]! ≤ nums2[stack_1[p]!]!) (invariant_nge_scanned_partition : ∀ j < nums2.size, (∃ u < i_2.size, i_2[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_partition_all : ∀ j < nums2.size, (∃ u < i_4.size, i_4[u]!.1 = nums2[j]!) ∨ ∃ p < stack_1.size, stack_1[p]! = j) (invariant_final_s_bound : s_1 ≤ stack_1.size) (invariant_final_stack_prefix_mapped : ∀ p < s_1, ∃ u < i_4.size, i_4[u]!.1 = nums2[stack_1[p]!]! ∧ i_4[u]!.2 = -OfNat.ofNat 1) (invariant_ans_a_bound : i_6 ≤ nums1.size) (invariant_ans_out_size : out_1.size = nums1.size) (invariant_ans_out_prefix_via_mp : ∀ k < i_6, ∃ u < i_4.size, i_4[u]!.1 = nums1[k]! ∧ out_1[k]! = i_4[u]!.2) (invariant_ans_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (invariant_nge_mp_sound : ∀ t < i_2.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_2[t]!.1) ∧ ((i_2[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_2[t]!.2 = nums2[k]!)) (invariant_nge_i_bound : True) (done_1 : True) (invariant_final_mp_sound : ∀ t < i_4.size, ∃ j, (j < nums2.size ∧ nums2[j]! = i_4[t]!.1) ∧ ((i_4[t]!.2 = -OfNat.ofNat 1 ∧ ∀ (x : ℕ), j < x → x < nums2.size → nums2[j]! < nums2[x]! → ∃ x_1, j < x_1 ∧ x_1 < x ∧ nums2[j]! < nums2[x_1]!) ∨ ∃ k, (j < k ∧ k < nums2.size ∧ nums2[j]! < nums2[k]! ∧ ∀ (t : ℕ), j < t → t < k → nums2[t]! ≤ nums2[j]!) ∧ i_4[t]!.2 = nums2[k]!)) (done_3 : stack_1.size ≤ s_1) (done_4 : nums1.size ≤ i_6) : postcondition nums1 nums2 out_1 := by
  refine' ⟨ invariant_ans_out_size, _ ⟩;
  intro i hi
  obtain ⟨u, hu₁, hu₂⟩ := invariant_ans_out_prefix_via_mp i (by linarith);
  rcases invariant_final_mp_sound u hu₁ with ⟨ j, hj₁, hj₂ | ⟨ k, hk₁, hk₂ ⟩ ⟩ <;> simp_all +decide [ OccursAt, NextGreaterValue ];
  · use j; simp_all +decide [ HasNextGreater, NextGreaterIndex ] ;
  · use j;
    refine' ⟨ hj₁, Or.inr ⟨ k, _, _ ⟩ ⟩ <;> simp_all +decide [ NextGreaterIndex ]

end Proof