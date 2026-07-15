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
  let mut i : Nat := 0
  let mut found : Bool := false
  while (i < nums.size ∧ found = false)
    -- i stays within array bounds (needed for termination/array access reasoning)
    invariant "outer_i_le_size" i ≤ nums.size
    -- If we've set found, we witnessed equal elements, hence a duplicate exists
    invariant "outer_found_sound" (found = true → HasDuplicate nums)
    -- If not found yet, no duplicate has been seen with first index < i
    invariant "outer_notfound_noDup_prefix" (found = false →
      ∀ a b : Nat, a < b ∧ b < nums.size ∧ a < i → nums[a]! ≠ nums[b]!)
    decreasing nums.size - i
  do
    let mut j : Nat := i + 1
    while (j < nums.size ∧ found = false)
      -- i is a valid index throughout the inner scan
      invariant "inner_i_lt_size" i < nums.size
      -- j advances within bounds
      invariant "inner_j_le_size" j ≤ nums.size
      -- j never goes below i+1
      invariant "inner_i1_le_j" i + 1 ≤ j
      -- If found becomes true, a duplicate exists
      invariant "inner_found_sound" (found = true → HasDuplicate nums)
      -- Carry over: if not found, still no duplicate with first index < i
      invariant "inner_notfound_noDup_prefix" (found = false →
        ∀ a b : Nat, a < b ∧ b < nums.size ∧ a < i → nums[a]! ≠ nums[b]!)
      -- If not found, nums[i] differs from all checked nums[b] for i < b < j
      invariant "inner_notfound_noDup_i" (found = false →
        ∀ b : Nat, i < b ∧ b < j → nums[i]! ≠ nums[b]!)
      decreasing nums.size - j
    do
      if nums[i]! = nums[j]! then
        found := true
      else
        pure ()
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
    (invariant_inner_i_lt_size : i < nums.size)
    (invariant_inner_j_le_size : j ≤ nums.size)
    (invariant_inner_i1_le_j : i + OfNat.ofNat 1 ≤ j)
    (a_2 : j < nums.size)
    (if_pos : nums[i]! = nums[j]!)
    (invariant_outer_notfound_noDup_prefix : false = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!)
    (invariant_inner_notfound_noDup_i : false = false → ∀ (b : ℕ), i < b → b < j → nums[i]! ≠ nums[b]!)
    : HasDuplicate nums := by
    intros; expose_names; try simp_all; try grind

theorem goal_1
    (nums : Array ℤ)
    (i : ℕ)
    (j : ℕ)
    (invariant_inner_i_lt_size : i < nums.size)
    (invariant_inner_j_le_size : j ≤ nums.size)
    (invariant_inner_i1_le_j : i + OfNat.ofNat 1 ≤ j)
    (a_2 : j < nums.size)
    (if_neg : ¬nums[i]! = nums[j]!)
    (invariant_outer_notfound_noDup_prefix : false = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!)
    (invariant_inner_notfound_noDup_i : false = false → ∀ (b : ℕ), i < b → b < j → nums[i]! ≠ nums[b]!)
    : True → ∀ (b : ℕ), i < b → b < j + OfNat.ofNat 1 → ¬nums[i]! = nums[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_2
    (nums : Array ℤ)
    (i : ℕ)
    (invariant_inner_i_lt_size : i < nums.size)
    (i_1 : Bool)
    (j_1 : ℕ)
    (invariant_outer_notfound_noDup_prefix : false = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i → nums[a]! ≠ nums[b]!)
    (invariant_inner_j_le_size : j_1 ≤ nums.size)
    (invariant_inner_i1_le_j : i + OfNat.ofNat 1 ≤ j_1)
    (invariant_inner_notfound_noDup_i : i_1 = false → ∀ (b : ℕ), i < b → b < j_1 → nums[i]! ≠ nums[b]!)
    (done_2 : ¬(j_1 < nums.size ∧ i_1 = false))
    : i_1 = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i + OfNat.ofNat 1 → ¬nums[a]! = nums[b]! := by
    intros; expose_names; try simp_all; try grind

theorem goal_3
    (nums : Array ℤ)
    (i_1 : Bool)
    (i_2 : ℕ)
    (invariant_outer_found_sound : i_1 = true → HasDuplicate nums)
    (invariant_outer_i_le_size : i_2 ≤ nums.size)
    (invariant_outer_notfound_noDup_prefix : i_1 = false → ∀ (a b : ℕ), a < b → b < nums.size → a < i_2 → nums[a]! ≠ nums[b]!)
    (done_1 : ¬(i_2 < nums.size ∧ i_1 = false))
    : postcondition nums i_1 := by
    unfold postcondition
    cases i_1
    · -- i_1 = false
      have hnotlt : ¬ i_2 < nums.size := by
        intro hi
        apply done_1
        exact And.intro hi rfl
      have hsize : nums.size ≤ i_2 := Nat.le_of_not_lt hnotlt
      have hi2eq : i_2 = nums.size := Nat.le_antisymm invariant_outer_i_le_size hsize

      have noDup : ¬ HasDuplicate nums := by
        intro hdup
        rcases hdup with ⟨a, b, hab, hbsize, heq⟩
        have ha_i2 : a < i_2 := by
          have : a < nums.size := lt_trans hab hbsize
          simpa [hi2eq] using this
        have hneq : nums[a]! ≠ nums[b]! :=
          invariant_outer_notfound_noDup_prefix rfl a b hab hbsize ha_i2
        exact hneq heq

      constructor
      · constructor
        · intro ht
          exact False.elim (Bool.noConfusion ht)
        · intro hd
          exact False.elim (noDup hd)
      · constructor
        · intro _
          exact noDup
        · intro _
          rfl

    · -- i_1 = true
      have dup : HasDuplicate nums := invariant_outer_found_sound rfl
      constructor
      · constructor
        · intro _
          exact dup
        · intro _
          rfl
      · constructor
        · intro hf
          exact False.elim (Bool.noConfusion hf)
        · intro hnd
          exact False.elim (hnd dup)


prove_correct ContainsDuplicate by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i j invariant_inner_i_lt_size invariant_inner_j_le_size invariant_inner_i1_le_j a_2 if_pos invariant_outer_notfound_noDup_prefix invariant_inner_notfound_noDup_i)
  exact (goal_1 nums i j invariant_inner_i_lt_size invariant_inner_j_le_size invariant_inner_i1_le_j a_2 if_neg invariant_outer_notfound_noDup_prefix invariant_inner_notfound_noDup_i)
  exact (goal_2 nums i invariant_inner_i_lt_size i_1 j_1 invariant_outer_notfound_noDup_prefix invariant_inner_j_le_size invariant_inner_i1_le_j invariant_inner_notfound_noDup_i done_2)
  exact (goal_3 nums i_1 i_2 invariant_outer_found_sound invariant_outer_i_le_size invariant_outer_notfound_noDup_prefix done_1)
end Proof
