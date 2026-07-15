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
    217. Contains Duplicate: Determine whether an integer array contains any value at least twice.
    **Important: complexity should be O(n^2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array of integers `nums`.
    2. The output is a boolean.
    3. The output is `true` exactly when there exist two different indices i and j with i < j such that nums[i] = nums[j].
    4. The output is `false` exactly when for all indices i < j in range, nums[i] ≠ nums[j] (all elements are distinct).
    5. Edge cases: empty arrays and single-element arrays have no duplicates, so the result is false.
-/

-- There is a duplicate iff two different indices within bounds have equal elements.
def HasDuplicate (nums : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat), i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasDuplicate nums) ∧
  (result = false ↔ ¬ HasDuplicate nums)
end Specs

section Impl
def checkDupFrom (nums : Array Int) (i j : Nat) : Bool :=
  if hj : j < nums.size then
    if nums[i]! == nums[j]! then true
    else checkDupFrom nums i (j + 1)
  else false
termination_by nums.size - j

def checkDupOuter (nums : Array Int) (i : Nat) : Bool :=
  if hi : i + 1 < nums.size then
    if checkDupFrom nums i (i + 1) then true
    else checkDupOuter nums (i + 1)
  else false
termination_by nums.size - i

def implementation (nums : Array Int) : Bool :=
  checkDupOuter nums 0
end Impl

section TestCases
-- Test case 1: example 1
-- nums = [1,2,3,1] -> true

def test1_nums : Array Int := #[1, 2, 3, 1]
def test1_Expected : Bool := true

-- Test case 2: example 2
-- nums = [1,2,3,4] -> false

def test2_nums : Array Int := #[1, 2, 3, 4]
def test2_Expected : Bool := false

-- Test case 3: example 3 (multiple duplicates)

def test3_nums : Array Int := #[1, 1, 1, 3, 3, 4, 3, 2, 4, 2]
def test3_Expected : Bool := true

-- Test case 4: empty array

def test4_nums : Array Int := #[]
def test4_Expected : Bool := false

-- Test case 5: singleton array

def test5_nums : Array Int := #[42]
def test5_Expected : Bool := false

-- Test case 6: duplicates adjacent

def test6_nums : Array Int := #[7, 7]
def test6_Expected : Bool := true

-- Test case 7: duplicates non-adjacent with negatives

def test7_nums : Array Int := #[-1, 0, 1, 2, -1]
def test7_Expected : Bool := true

-- Test case 8: all distinct including negative and zero

def test8_nums : Array Int := #[-3, -2, -1, 0, 1, 2, 3]
def test8_Expected : Bool := false

-- Test case 9: many equal elements

def test9_nums : Array Int := #[5, 5, 5, 5]
def test9_Expected : Bool := true
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
  return (result : Bool)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    : ∀ (i j : ℕ), checkDupFrom nums i j = true ↔ ∃ k, j ≤ k ∧ k < nums.size ∧ nums[i]! = nums[k]! := by
    intro i
    suffices h : ∀ (n : ℕ) (j : ℕ), nums.size - j = n → (checkDupFrom nums i j = true ↔ ∃ k, j ≤ k ∧ k < nums.size ∧ nums[i]! = nums[k]!) by
      intro j; exact h (nums.size - j) j rfl
    intro n
    induction n with
    | zero =>
      intro j hj
      unfold checkDupFrom
      split
      · omega
      · constructor
        · intro h; exact absurd h Bool.false_ne_true
        · rintro ⟨k, hk1, hk2, hk3⟩; omega
    | succ n ih =>
      intro j hj
      unfold checkDupFrom
      split
      · rename_i hlt
        split
        · rename_i heq
          constructor
          · intro _
            exact ⟨j, Nat.le_refl j, hlt, by rw [beq_iff_eq] at heq; exact heq⟩
          · intro _; rfl
        · rename_i hneq
          have hij : nums.size - (j + 1) = n := by omega
          rw [ih (j + 1) hij]
          constructor
          · rintro ⟨k, hk1, hk2, hk3⟩
            exact ⟨k, by omega, hk2, hk3⟩
          · rintro ⟨k, hk1, hk2, hk3⟩
            rcases Nat.eq_or_lt_of_le hk1 with rfl | hgt
            · exfalso
              rw [beq_iff_eq] at hneq
              exact hneq hk3
            · exact ⟨k, by omega, hk2, hk3⟩
      · rename_i hge
        constructor
        · intro h; exact absurd h Bool.false_ne_true
        · rintro ⟨k, hk1, hk2, hk3⟩; omega

theorem correctness_goal_1
    (nums : Array ℤ)
    (h_from : ∀ (i j : ℕ), checkDupFrom nums i j = true ↔ ∃ k, j ≤ k ∧ k < nums.size ∧ nums[i]! = nums[k]!)
    : ∀ (i : ℕ), checkDupOuter nums i = true ↔ ∃ i' j, i ≤ i' ∧ i' < j ∧ j < nums.size ∧ nums[i']! = nums[j]! := by
    intro i
    induction h_term : nums.size - i using Nat.strongRecOn generalizing i with
    | _ n ih =>
    constructor
    · -- Forward: checkDupOuter = true → ∃ ...
      intro h_outer
      unfold checkDupOuter at h_outer
      split at h_outer
      case isTrue hi =>
        split at h_outer
        case isTrue h_from_true =>
          rw [h_from] at h_from_true
          obtain ⟨k, hk1, hk2, hk3⟩ := h_from_true
          exact ⟨i, k, Nat.le_refl i, by omega, hk2, hk3⟩
        case isFalse h_from_false =>
          have h_sub : nums.size - (i + 1) < n := by omega
          have ih' := ih _ h_sub (i + 1) rfl
          rw [ih'] at h_outer
          obtain ⟨i', j, hi'1, hi'2, hi'3, hi'4⟩ := h_outer
          exact ⟨i', j, by omega, hi'2, hi'3, hi'4⟩
      case isFalse hi =>
        simp at h_outer
    · -- Backward: ∃ ... → checkDupOuter = true
      intro ⟨i', j, hi'1, hi'2, hi'3, hi'4⟩
      unfold checkDupOuter
      split
      case isTrue hi =>
        split
        case isTrue => rfl
        case isFalse h_from_false =>
          have h_sub : nums.size - (i + 1) < n := by omega
          have ih' := ih _ h_sub (i + 1) rfl
          rw [ih']
          rcases Nat.eq_or_lt_of_le hi'1 with rfl | hi'_gt
          · -- i' = i
            exfalso
            apply h_from_false
            rw [h_from]
            exact ⟨j, by omega, hi'3, hi'4⟩
          · -- i + 1 ≤ i'
            exact ⟨i', j, by omega, hi'2, hi'3, hi'4⟩
      case isFalse hi =>
        omega

theorem correctness_goal
    (nums : Array Int)
    : postcondition nums (implementation nums) := by
    have h_from : ∀ (i j : Nat), checkDupFrom nums i j = true ↔ ∃ k, j ≤ k ∧ k < nums.size ∧ nums[i]! = nums[k]! := by expose_names; exact (correctness_goal_0 nums)
    have h_outer : ∀ (i : Nat), checkDupOuter nums i = true ↔ ∃ i' j, i ≤ i' ∧ i' < j ∧ j < nums.size ∧ nums[i']! = nums[j]! := by expose_names; exact (correctness_goal_1 nums h_from)
    unfold postcondition implementation
    constructor
    · constructor
      · intro h
        rw [h_outer] at h
        obtain ⟨i', j, _, hij, hjn, heq⟩ := h
        exact ⟨i', j, hij, hjn, heq⟩
      · intro ⟨i, j, hij, hjn, heq⟩
        rw [h_outer]
        exact ⟨i, j, Nat.zero_le _, hij, hjn, heq⟩
    · rw [Bool.eq_false_iff]
      constructor
      · intro hne hdup
        apply hne
        rw [h_outer]
        obtain ⟨i, j, hij, hjn, heq⟩ := hdup
        exact ⟨i, j, Nat.zero_le _, hij, hjn, heq⟩
      · intro hnd
        intro heq
        apply hnd
        rw [h_outer] at heq
        obtain ⟨i', j, _, hij, hjn, he⟩ := heq
        exact ⟨i', j, hij, hjn, he⟩
end Proof
