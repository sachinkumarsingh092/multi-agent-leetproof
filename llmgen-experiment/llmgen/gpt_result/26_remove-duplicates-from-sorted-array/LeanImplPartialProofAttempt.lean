import Lean
import Mathlib.Tactic
import Velvet.Std

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
  -- Pure functional two-pointer scan building an output array.
  if h0 : nums.size = 0 then
    (0, nums)
  else
    let first := nums[0]!
    let initOut : Array Int :=
      -- start with the first element, then pad to the original size with 0s
      (#[first]).append (Array.mkArray (nums.size - 1) 0)
    let rec go (i : Nat) (k : Nat) (last : Int) (out : Array Int) : Nat × Array Int :=
      if h : i < nums.size then
        let x := nums[i]!
        if x = last then
          go (i + 1) k last out
        else
          let out' := out.set! k x
          go (i + 1) (k + 1) x out'
      else
        (k, out)
    -- We already placed nums[0] at position 0, so start scanning from i = 1 with k = 1.
    go 1 1 first initOut
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

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h0 : ¬nums.size = 0)
    : (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2.size = nums.size ∧
  PrefixStrictIncreasing (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2
      (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).1 ∧
    PrefixSameMembers nums (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).1
      (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2 := by
    classical
    unfold implementation.go
    -- after unfolding once, stop
    admit

theorem correctness_goal_1
    (nums : Array ℤ)
    (h_precond : precondition nums)
    (h_go_main : (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2.size = nums.size ∧
  PrefixStrictIncreasing (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2
      (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).1 ∧
    PrefixSameMembers nums (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).1
      (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2)
    : PrefixOccursInOrderFirst nums (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).2
  (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)).1 := by
  classical

  let res := implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ mkArray (nums.size - 1) 0)
  let k : Nat := res.1
  let out : Array ℤ := res.2

  have h_go_main' : out.size = nums.size ∧ PrefixStrictIncreasing out k ∧ PrefixSameMembers nums k out := by
    simpa [res, k, out] using h_go_main
  rcases h_go_main' with ⟨Hsize, Hstrict, Hmem⟩

  have Hsorted : ArraySortedLe nums := by
    simpa [precondition] using h_precond

  rcases Hstrict with ⟨Hk_out, Hout_adj⟩
  rcases Hmem with ⟨_Hk_out2, Hmem_iff⟩

  -- From adjacent strict increase, get strict increase for any i<j<k.
  have out_lt : ∀ {i j : Nat}, i < j → j < k → out[i]! < out[j]! := by
    intro i j hij hjk
    have hij1 : i + 1 ≤ j := Nat.succ_le_of_lt hij
    let P : Nat → Prop := fun n => n < k → out[i]! < out[n]!
    have hbase : P (i + 1) := by
      intro hi1k
      simpa using (Hout_adj i hi1k)
    have hstep : ∀ n, i + 1 ≤ n → P n → P (n + 1) := by
      intro n _ hn
      intro hn1k
      have hnk : n < k := lt_trans (Nat.lt_succ_self n) hn1k
      have hi_lt_n : out[i]! < out[n]! := hn hnk
      have hn_lt : out[n]! < out[n + 1]! := by
        simpa using (Hout_adj n hn1k)
      exact lt_trans hi_lt_n hn_lt
    have hjP : P j := Nat.le_induction hbase hstep j hij1
    exact hjP hjk

  -- From adjacent sortedness, get monotonicity for any i<j.
  have nums_mono : ∀ {i j : Nat}, i < j → j < nums.size → nums[i]! ≤ nums[j]! := by
    intro i j hij hj
    have hij1 : i + 1 ≤ j := Nat.succ_le_of_lt hij
    let P : Nat → Prop := fun n => n < nums.size → nums[i]! ≤ nums[n]!
    have hbase : P (i + 1) := by
      intro hi1
      simpa using (Hsorted i hi1)
    have hstep : ∀ n, i + 1 ≤ n → P n → P (n + 1) := by
      intro n _ hn
      intro hn1
      have hnlt : n < nums.size := lt_trans (Nat.lt_succ_self n) hn1
      have hi_le_n : nums[i]! ≤ nums[n]! := hn hnlt
      have hn_le : nums[n]! ≤ nums[n + 1]! := by
        simpa using (Hsorted n hn1)
      exact le_trans hi_le_n hn_le
    have hjP : P j := Nat.le_induction hbase hstep j hij1
    exact hjP hj

  -- Every prefix element of `out` occurs in `nums`.
  have hex : ∀ i : Nat, i < k → ∃ j : Nat, j < nums.size ∧ nums[j]! = out[i]! := by
    intro i hi
    have mem_x : out[i]! ∈ nums := by
      exact (Hmem_iff (out[i]!)).2 ⟨i, hi, rfl⟩
    rcases Array.getElem?_of_mem mem_x with ⟨j, hjget⟩
    have hjlt : j < nums.size := by
      rcases (Array.getElem?_eq_some_iff (xs := nums) (i := j) (b := out[i]!)).1 hjget with ⟨hjlt, _⟩
      exact hjlt
    have hjval : nums[j]! = out[i]! := by
      simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hjget]
    exact ⟨j, hjlt, hjval⟩

  -- Define f i = first index in nums where out[i] occurs (for i<k).
  let f : Nat → Nat := fun i => if hi : i < k then Nat.find (hex i hi) else 0

  have h_main : PrefixOccursInOrderFirst nums out k := by
    refine ⟨f, ?_, ?_, ?_⟩

    · intro i hi
      have hfi : f i = Nat.find (hex i hi) := by simp [f, hi]
      have hspec := Nat.find_spec (hex i hi)
      refine ⟨?_, ?_⟩
      · simpa [hfi] using hspec.1
      · simpa [hfi] using (Eq.symm hspec.2)

    · intro i j hij hjk
      have hik : i < k := lt_trans hij hjk
      have hfi_spec := Nat.find_spec (hex i hik)
      have hfj_spec := Nat.find_spec (hex j hjk)
      have hfi_eq : f i = Nat.find (hex i hik) := by simp [f, hik]
      have hfj_eq : f j = Nat.find (hex j hjk) := by simp [f, hjk]

      have houtlt : out[i]! < out[j]! := out_lt hij hjk

      have : ¬ f j ≤ f i := by
        intro hle
        have hle_vals : nums[f j]! ≤ nums[f i]! := by
          cases lt_or_eq_of_le hle with
          | inl hlt =>
              have hfi_lt : f i < nums.size := by simpa [hfi_eq] using hfi_spec.1
              exact nums_mono hlt hfi_lt
          | inr heq =>
              simpa [heq]

        have houtle : out[j]! ≤ out[i]! := by
          have hfi_val : nums[f i]! = out[i]! := by simpa [hfi_eq] using hfi_spec.2
          have hfj_val : nums[f j]! = out[j]! := by simpa [hfj_eq] using hfj_spec.2
          simpa [hfj_val, hfi_val] using hle_vals

        exact (not_le_of_gt houtlt) houtle

      exact lt_of_not_ge this

    · intro i hi j hj
      have hfi_eq : f i = Nat.find (hex i hi) := by simp [f, hi]
      have hspec := Nat.find_spec (hex i hi)
      have hfi_lt : f i < nums.size := by
        simpa [hfi_eq] using hspec.1
      have hjlt : j < nums.size := lt_trans hj hfi_lt

      have hminAll : ∀ m < Nat.find (hex i hi), ¬(m < nums.size ∧ nums[m]! = out[i]!) :=
        (Nat.le_find_iff (hex i hi) (Nat.find (hex i hi))).1 (le_rfl)

      have hjfind : j < Nat.find (hex i hi) := by
        simpa [hfi_eq] using hj

      have hnot : ¬(j < nums.size ∧ nums[j]! = out[i]!) := hminAll j hjfind

      intro hEq
      exact hnot ⟨hjlt, hEq⟩

  simpa [res, k, out] using h_main

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation (nums)) := by
  classical
  by_cases h0 : nums.size = 0
  · -- empty input
    have hnomem : ∀ (x : Int), x ∉ nums := by
      expose_names; intros; expose_names; try simp_all; try grind
    simp [implementation, postcondition, PrefixStrictIncreasing, PrefixSameMembers, PrefixOccursInOrderFirst, h0, hnomem]
  · -- nonempty input
    have h_go_main :
        (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).2.size = nums.size ∧
        PrefixStrictIncreasing
          (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).2
          (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).1 ∧
        PrefixSameMembers nums
          (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).1
          (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).2 := by
      expose_names; exact (correctness_goal_0 nums h_precond h0)
    have h_order_first :
        PrefixOccursInOrderFirst nums
          (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).2
          (implementation.go nums 1 1 nums[0]! (#[nums[0]!] ++ Array.mkArray (nums.size - 1) 0)).1 := by
      expose_names; exact (correctness_goal_1 nums h_precond h_go_main)
    -- conclude
    rcases h_go_main with ⟨hsize, hinc, hmem⟩
    have : postcondition nums (implementation nums) := by
      simp [implementation, postcondition, h0, hsize, hinc, hmem, h_order_first]
    exact this
end Proof
