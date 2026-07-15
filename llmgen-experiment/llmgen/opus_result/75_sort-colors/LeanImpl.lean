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
    SortColors: Given an array of colors encoded as 0, 1, 2, reorder it so that all 0s come first,
    then all 1s, then all 2s.
    Natural language breakdown:
    1. The input is an array `nums` of natural numbers that represent colors.
    2. Only the values 0, 1, and 2 are valid colors.
    3. The output must have the same length as the input.
    4. The output must contain the same multiset of elements as the input (no loss/duplication).
    5. The output must be ordered so that every 0 appears before every 1 and every 1 before every 2.
    6. Equivalently, there exist boundaries a ≤ b such that indices < a are 0, indices in [a,b) are 1,
       and indices ≥ b are 2.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

-- Helper: all entries are in {0,1,2}
def ColorsOnly (nums : Array Nat) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≤ 2

-- Helper: array is partitioned into 0s then 1s then 2s
-- This avoids referencing any particular algorithm while fully characterizing the desired order.
def Is012Sorted (nums : Array Nat) : Prop :=
  ∃ (a : Nat) (b : Nat),
    a ≤ b ∧ b ≤ nums.size ∧
    (∀ (i : Nat), i < a → nums[i]! = 0) ∧
    (∀ (i : Nat), a ≤ i ∧ i < b → nums[i]! = 1) ∧
    (∀ (i : Nat), b ≤ i ∧ i < nums.size → nums[i]! = 2)

-- Helper: count occurrences of a value in an array
-- (Array.count is available when DecidableEq is available.)
def countVal (nums : Array Nat) (v : Nat) : Nat :=
  nums.count v

-- Preconditions: input must contain only 0/1/2.
def precondition (nums : Array Nat) : Prop :=
  ColorsOnly nums

-- Postconditions: result has same size, is ordered as 0-then-1-then-2,
-- and preserves the counts of 0,1,2 from the input.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  result.size = nums.size ∧
  Is012Sorted result ∧
  countVal result 0 = countVal nums 0 ∧
  countVal result 1 = countVal nums 1 ∧
  countVal result 2 = countVal nums 2
end Specs

section Impl
def implementation (nums : Array Nat) : Array Nat :=
  let c0 := nums.count 0
  let c1 := nums.count 1
  let c2 := nums.count 2
  mkArray c0 0 ++ mkArray c1 1 ++ mkArray c2 2
end Impl

section TestCases
-- Test case 1: Example 1 from the problem statement
-- Input: [2,0,2,1,1,0] Output: [0,0,1,1,2,2]
def test1_nums : Array Nat := #[2, 0, 2, 1, 1, 0]
def test1_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 2: Example 2 from the problem statement
-- Input: [2,0,1] Output: [0,1,2]
def test2_nums : Array Nat := #[2, 0, 1]
def test2_Expected : Array Nat := #[0, 1, 2]

-- Test case 3: Empty array (degenerate but valid)
def test3_nums : Array Nat := #[]
def test3_Expected : Array Nat := #[]

-- Test case 4: Singleton 0
def test4_nums : Array Nat := #[0]
def test4_Expected : Array Nat := #[0]

-- Test case 5: Singleton 1
def test5_nums : Array Nat := #[1]
def test5_Expected : Array Nat := #[1]

-- Test case 6: Singleton 2
def test6_nums : Array Nat := #[2]
def test6_Expected : Array Nat := #[2]

-- Test case 7: Already sorted with repeats
def test7_nums : Array Nat := #[0, 0, 1, 1, 2, 2]
def test7_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 8: Reverse sorted
def test8_nums : Array Nat := #[2, 2, 1, 1, 0, 0]
def test8_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 9: Mixed small (extra diversity)
def test9_nums : Array Nat := #[1, 0, 2, 0, 1]
def test9_Expected : Array Nat := #[0, 0, 1, 1, 2]

-- Recommend to validate: precondition, postcondition, SortColors
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
method implementationPbt (nums : Array Nat)
  return (result : Array Nat)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (nums : Array ℕ)
    (h_precond : precondition nums)
    : Array.count 0 nums + Array.count 1 nums + Array.count 2 nums = nums.size := by
    unfold precondition ColorsOnly at h_precond
    have key : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 2) → 
      l.count 0 + l.count 1 + l.count 2 = l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        have hx : x ≤ 2 := hl x (List.mem_cons_self ..)
        have hxs : ∀ y ∈ xs, y ≤ 2 := fun y hy => hl y (List.mem_cons_of_mem _ hy)
        simp [List.count_cons, List.length_cons]
        have := ih hxs
        interval_cases x <;> simp_all <;> omega
    rw [← Array.count_toList, ← Array.count_toList, ← Array.count_toList, ← Array.length_toList]
    apply key
    intro x hx
    rw [Array.mem_toList] at hx
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
    have h := h_precond i hi
    simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_eq_getElem hi, dif_pos hi] at h
    exact h

theorem correctness_goal_1_0
    (nums : Array ℕ)
    : (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size =
  Array.count 0 nums + Array.count 1 nums + Array.count 2 nums := by
    simp [Array.size_append, Array.size_mkArray, mkArray]
    omega

theorem correctness_goal_1_1
    (nums : Array ℕ)
    (h_bridge : Array.count 0 nums + Array.count 1 nums + Array.count 2 nums = nums.size)
    (hsize : (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size =
  Array.count 0 nums + Array.count 1 nums + Array.count 2 nums)
    : ∀ i < Array.count 0 nums,
  (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2)[i]! = 0 := by
    intro i hi
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_append_left]
    · rw [Array.getElem?_append_left]
      · simp [Array.getElem?_replicate, hi, mkArray]
      · simp [mkArray]; exact hi
    · simp [mkArray]; omega

theorem correctness_goal_1_2
    (nums : Array ℕ)
    (h_bridge : Array.count 0 nums + Array.count 1 nums + Array.count 2 nums = nums.size)
    (hsize : (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size =
  Array.count 0 nums + Array.count 1 nums + Array.count 2 nums)
    : ∀ (i : ℕ),
  Array.count 0 nums ≤ i ∧ i < Array.count 0 nums + Array.count 1 nums →
    (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2)[i]! = 1 := by
    intro i ⟨hle, hlt⟩
    set c0 := Array.count 0 nums
    set c1 := Array.count 1 nums
    set c2 := Array.count 2 nums
    set arr := mkArray c0 0 ++ mkArray c1 1 ++ mkArray c2 2
    have hi_lt : i < arr.size := by omega
    rw [Array.getElem!_eq_getD]
    have hgetD : arr.getD i default = arr[i]'hi_lt := by
      unfold Array.getD
      split
      · next h => rfl
      · next h => exact absurd hi_lt h
    rw [hgetD]
    have hsize_mk0 : (mkArray c0 (0 : ℕ)).size = c0 := Array.size_mkArray
    have hsize_mk1 : (mkArray c1 (1 : ℕ)).size = c1 := Array.size_mkArray
    have hsize_left : (mkArray c0 0 ++ mkArray c1 1).size = c0 + c1 := by
      rw [Array.size_append, hsize_mk0, hsize_mk1]
    have hlt' : i < (mkArray c0 0 ++ mkArray c1 1).size := by omega
    show (mkArray c0 0 ++ mkArray c1 1 ++ mkArray c2 2)[i] = 1
    rw [Array.getElem_append_left hlt']
    have hge : ¬ (i < (mkArray c0 (0 : ℕ)).size) := by omega
    rw [Array.getElem_append]
    simp only [hge, ↓reduceDIte]
    have h_idx_bound : i - (mkArray c0 (0 : ℕ)).size < (mkArray c1 (1 : ℕ)).size := by omega
    exact Array.getElem_replicate h_idx_bound

theorem correctness_goal_1_3
    (nums : Array ℕ)
    (h_bridge : Array.count 0 nums + Array.count 1 nums + Array.count 2 nums = nums.size)
    (hsize : (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size =
  Array.count 0 nums + Array.count 1 nums + Array.count 2 nums)
    : ∀ (i : ℕ),
  Array.count 0 nums + Array.count 1 nums ≤ i ∧
      i < (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size →
    (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2)[i]! = 2 := by
    intro i ⟨hle, hlt⟩
    set c0 := Array.count 0 nums
    set c1 := Array.count 1 nums
    set c2 := Array.count 2 nums
    set arr := mkArray c0 0 ++ mkArray c1 1 ++ mkArray c2 2
    have hsz : arr.size = c0 + c1 + c2 := hsize
    have hleft_sz : (mkArray c0 0 ++ mkArray c1 1).size = c0 + c1 := by
      simp [Array.size_append, mkArray, List.length_replicate]
    have hidx : i - (c0 + c1) < c2 := by omega
    have hq : arr[i]? = some 2 := by
      show ((mkArray c0 0 ++ mkArray c1 1) ++ mkArray c2 2)[i]? = some 2
      rw [Array.getElem?_append_right (by omega)]
      rw [hleft_sz]
      rw [← Array.getElem?_toList]
      simp [mkArray, List.getElem?_replicate, hidx]
    rw [Array.getElem!_eq_getD, Array.getD]
    split
    · rename_i h
      have heq : arr[i]? = some (arr[i]) := by simp [Array.getElem?_eq_some_iff]
      rw [heq] at hq
      exact Option.some.inj hq
    · exfalso; omega

theorem correctness_goal_1
    (nums : Array ℕ)
    (h_bridge : Array.count 0 nums + Array.count 1 nums + Array.count 2 nums = nums.size)
    : Is012Sorted (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2) := by
    have hsize : (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size = Array.count 0 nums + Array.count 1 nums + Array.count 2 nums := by expose_names; exact (correctness_goal_1_0 nums)
    have h_zeros : ∀ (i : Nat), i < Array.count 0 nums → (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2)[i]! = 0 := by expose_names; exact (correctness_goal_1_1 nums h_bridge hsize)
    have h_ones : ∀ (i : Nat), Array.count 0 nums ≤ i ∧ i < Array.count 0 nums + Array.count 1 nums → (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2)[i]! = 1 := by expose_names; exact (correctness_goal_1_2 nums h_bridge hsize)
    have h_twos : ∀ (i : Nat), Array.count 0 nums + Array.count 1 nums ≤ i ∧ i < (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2).size → (mkArray (Array.count 0 nums) 0 ++ mkArray (Array.count 1 nums) 1 ++ mkArray (Array.count 2 nums) 2)[i]! = 2 := by expose_names; exact (correctness_goal_1_3 nums h_bridge hsize)
    exact ⟨Array.count 0 nums, Array.count 0 nums + Array.count 1 nums, by omega, by (rw [hsize]; omega), h_zeros, h_ones, h_twos⟩

theorem correctness_goal
    (nums : Array Nat)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
    unfold postcondition implementation precondition ColorsOnly at *
    simp only []
    have h_bridge : nums.count 0 + nums.count 1 + nums.count 2 = nums.size := by expose_names; exact (correctness_goal_0 nums h_precond)
    have h_sorted : Is012Sorted (mkArray (nums.count 0) 0 ++ mkArray (nums.count 1) 1 ++ mkArray (nums.count 2) 2) := by expose_names; exact (correctness_goal_1 nums h_bridge)
    have h_mkArray_replicate : ∀ (n : Nat) (v : Nat), mkArray n v = Array.replicate n v := by expose_names; intros; expose_names; rfl
    simp only [h_mkArray_replicate] at h_sorted ⊢
    refine ⟨?_, h_sorted, ?_, ?_, ?_⟩
    · simp [Array.size_append, Array.size_replicate, h_bridge]; omega
    · simp [countVal, Array.count_append, Array.count_replicate]
    · simp [countVal, Array.count_append, Array.count_replicate]
    · simp [countVal, Array.count_append, Array.count_replicate]
end Proof
