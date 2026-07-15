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
    217. Contains Duplicate: Determine whether an integer array contains any value at least twice.
    **Important: complexity should be O(n^2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array of integers `nums`.
    2. The output is a boolean.
    3. The output is `true` exactly when there exist two different indices i and j with i < j such that nums[i] = nums[j].
    4. The output is `false` exactly when for all indices i < j in range, nums[i] ≠ nums[j] (all elements are distinct).
    5. Edge cases: empty arrays and single-element arrays have no duplicates, so the result is false.
-/

section Specs
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
method ContainsDuplicate (nums: Array Int)
  return (result: Bool)
  require precondition nums
  ensures postcondition nums result
  do
  let mut found := false
  let mut i := 0
  while i < nums.size
    -- i is bounded: initialized to 0, incremented up to nums.size
    invariant "i_bound" 0 ≤ i ∧ i ≤ nums.size
    -- If found is true, a duplicate exists in nums
    invariant "found_implies_dup" found = true → HasDuplicate nums
    -- If found is false, no duplicate pair with first index < i has been found
    invariant "no_dup_so_far" found = false → ∀ a b, a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!
    decreasing nums.size - i
  do
    let mut j := i + 1
    while j < nums.size
      -- j is bounded between i+1 and nums.size
      invariant "j_bound" i + 1 ≤ j ∧ j ≤ nums.size
      -- i is still a valid index in the inner loop
      invariant "i_bound_inner" 0 ≤ i ∧ i < nums.size
      -- If found is true, a duplicate exists in nums
      invariant "inner_found_implies_dup" found = true → HasDuplicate nums
      -- If found is false, no duplicate pair with first index < i
      invariant "inner_no_dup_prev" found = false → ∀ a b, a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!
      -- If found is false, no duplicate pair (i, b) for b in [i+1, j)
      invariant "inner_no_dup_cur" found = false → ∀ b, i < b → b < j → nums[i]! ≠ nums[b]!
      decreasing nums.size - j
    do
      if nums[i]! = nums[j]! then
        found := true
      j := j + 1
    i := i + 1
  return found
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

#assert_same_evaluation #[((ContainsDuplicate test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((ContainsDuplicate test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((ContainsDuplicate test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((ContainsDuplicate test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((ContainsDuplicate test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((ContainsDuplicate test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((ContainsDuplicate test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((ContainsDuplicate test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((ContainsDuplicate test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test ContainsDuplicate (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (a_2 : i + OfNat.ofNat 1 ≤ j)
    (if_pos_1 : j < nums.size)
    (if_pos_2 : nums[i]! = nums[j]!)
    : ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! = nums[j]! := by
    have h : i < j := by
      have : OfNat.ofNat 1 = (1 : ℕ) := rfl
      omega
    exact ⟨i, j, h, if_pos_1, if_pos_2⟩

theorem goal_1
    (nums : Array ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_found_implies_dup : found = true → ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!)
    (found_1 : Bool)
    (j : ℕ)
    (a_2 : i + OfNat.ofNat 1 ≤ j)
    (a_3 : j ≤ nums.size)
    (a_5 : i < nums.size)
    (invariant_inner_no_dup_prev : found_1 = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i → ¬nums[a]! = nums[b]!)
    (invariant_inner_no_dup_cur : found_1 = false → ∀ (b : ℕ), i < b → b < j → ¬nums[i]! = nums[b]!)
    (if_pos_1 : j < nums.size)
    (if_neg : ¬nums[i]! = nums[j]!)
    : found_1 = false → ∀ (b : ℕ), i < b → b < j + OfNat.ofNat 1 → ¬nums[i]! = nums[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_2
    (nums : Array ℤ)
    (found : Bool)
    (i : ℕ)
    (invariant_found_implies_dup : found = true → ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!)
    (a_5 : i < nums.size)
    (i_1 : Bool)
    (j_1 : ℕ)
    (invariant_inner_no_dup_prev : i_1 = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i → ¬nums[a]! = nums[b]!)
    (a_2 : i + OfNat.ofNat 1 ≤ j_1)
    (a_3 : j_1 ≤ nums.size)
    (invariant_inner_no_dup_cur : i_1 = false → ∀ (b : ℕ), i < b → b < j_1 → ¬nums[i]! = nums[b]!)
    (done_2 : nums.size ≤ j_1)
    : i_1 = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i + OfNat.ofNat 1 → ¬nums[a]! = nums[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (nums : Array ℤ)
    (i_1 : Bool)
    (i_2 : ℕ)
    (invariant_found_implies_dup : i_1 = true → ∃ i j, i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!)
    (a_1 : i_2 ≤ nums.size)
    (invariant_no_dup_so_far : i_1 = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i_2 → ¬nums[a]! = nums[b]!)
    (done_1 : nums.size ≤ i_2)
    : postcondition nums i_1 := by
    have h_eq : i_2 = nums.size := Nat.le_antisymm a_1 done_1
    unfold postcondition HasDuplicate
    constructor
    · constructor
      · intro h; exact invariant_found_implies_dup h
      · intro ⟨i, j, hij, hjn, heq⟩
        by_contra h_not_true
        have h_false : i_1 = false := by cases i_1 <;> simp_all
        have h_no_dup := invariant_no_dup_so_far h_false i j hij hjn (by omega)
        exact h_no_dup heq
    · constructor
      · intro h_false
        intro ⟨i, j, hij, hjn, heq⟩
        have h_no_dup := invariant_no_dup_so_far h_false i j hij hjn (by omega)
        exact h_no_dup heq
      · intro h_no_dup
        by_contra h_not_false
        have h_true : i_1 = true := by cases i_1 <;> simp_all
        exact h_no_dup (invariant_found_implies_dup h_true)


prove_correct ContainsDuplicate by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i j a_2 if_pos_1 if_pos_2)
  exact (goal_1 nums found i invariant_found_implies_dup found_1 j a_2 a_3 a_5 invariant_inner_no_dup_prev invariant_inner_no_dup_cur if_pos_1 if_neg)
  exact (goal_2 nums found i invariant_found_implies_dup a_5 i_1 j_1 invariant_inner_no_dup_prev a_2 a_3 invariant_inner_no_dup_cur done_2)
  exact (goal_3 nums i_1 i_2 invariant_found_implies_dup a_1 invariant_no_dup_so_far done_1)
end Proof
