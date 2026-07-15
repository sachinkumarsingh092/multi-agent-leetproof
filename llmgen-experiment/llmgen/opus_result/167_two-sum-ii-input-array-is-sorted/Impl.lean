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
    TwoSumIISorted: Given a 1-indexed sorted array of integers, return the (1-indexed) positions of
    the unique pair of distinct elements whose sum equals a target.
    Natural language breakdown:
    1. Input is an array `numbers : Array Int` sorted in non-decreasing order.
    2. We are given an integer `target : Int`.
    3. There exist indices i and j with 0 ≤ i < j < numbers.size such that numbers[i] + numbers[j] = target.
    4. The problem guarantees this pair is unique (exactly one solution).
    5. Output is an array of length 2 containing the 1-based indices: [i+1, j+1].
    6. The two indices must be strictly increasing and within 1..numbers.size.
    7. We must not use the same element twice (captured by i < j).
    Your algorithm should run in **O(n)** time and **O(1)** extra space.
-/

section Specs
-- Helper: non-decreasing order on an Int array.
-- We use the standard relational characterization of sortedness by indices.
def isSortedNondecreasing (numbers : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!

-- Helper: a valid 0-based pair (i,j) witnessing the target sum.
def isWitnessPair (numbers : Array Int) (target : Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target

-- Helper: uniqueness of the witness pair, expressed over 0-based indices.
def hasUniqueWitnessPair (numbers : Array Int) (target : Int) : Prop :=
  (∃ (i : Nat) (j : Nat), isWitnessPair numbers target i j) ∧
  (∀ (i₁ : Nat) (j₁ : Nat) (i₂ : Nat) (j₂ : Nat),
    isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)

-- Helper: output shape/validity and correspondence to a witness pair.
def outputMatchesUniquePair (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  result.size = 2 ∧
  (1 ≤ result[0]!) ∧ (result[0]! < result[1]!) ∧ (result[1]! ≤ numbers.size) ∧
  (numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target) ∧
  (∀ (i : Nat) (j : Nat), isWitnessPair numbers target i j →
    result[0]! = i + 1 ∧ result[1]! = j + 1)

-- Preconditions
-- We keep them simple and decidable-ish (arith + array bounds), and capture the problem guarantees.
def precondition (numbers : Array Int) (target : Int) : Prop :=
  numbers.size ≥ 2 ∧
  isSortedNondecreasing numbers ∧
  hasUniqueWitnessPair numbers target

-- Postconditions
-- Ensure the result is exactly the 1-based indices of the unique witness pair.
def postcondition (numbers : Array Int) (target : Int) (result : Array Nat) : Prop :=
  outputMatchesUniquePair numbers target result
end Specs

section Impl
method TwoSumIISorted (numbers : Array Int) (target : Int)
  return (result : Array Nat)
  require precondition numbers target
  ensures postcondition numbers target result
  do
  let mut left := 0
  let mut right := numbers.size - 1
  let mut res : Array Nat := #[0, 0]
  while left < right
    -- Inv 1: res always has size 2
    invariant "res_size" res.size = 2
    -- Inv 2: right is a valid index
    invariant "right_bound" right < numbers.size
    -- Inv 3: left is bounded
    invariant "left_bound" left ≤ numbers.size
    -- Inv 4: left ≤ right (pointers never cross)
    invariant "left_le_right" left ≤ right
    -- Inv 5: the key narrowing invariant — the unique witness pair is either
    -- still within [left, right] or we've already captured it in res.
    -- Init: at start left=0, right=size-1, and precondition gives existence of witness pair within bounds.
    -- Preservation: sorted array property ensures narrowing preserves reachability.
    -- Sufficiency: on exit (left ≥ right), if pair were in [left,right] then left ≤ i < j ≤ right
    --   implies left < right, contradiction. So postcondition must hold.
    invariant "witness_reachable" ∀ i j, isWitnessPair numbers target i j →
      (left ≤ i ∧ j ≤ right) ∨ (postcondition numbers target res)
    -- Decreasing: right - left shrinks each iteration (found: left becomes right;
    -- s < target: left++; s > target: right--)
    decreasing right - left
  do
    let s := numbers[left]! + numbers[right]!
    if s = target then
      res := #[left + 1, right + 1]
      left := right -- force loop exit
    else
      if s < target then
        left := left + 1
      else
        right := right - 1
  return res
end Impl

section TestCases
-- Test case 1: Example 1
-- numbers = [2,7,11,15], target = 9 => [1,2]
def test1_numbers : Array Int := #[2, 7, 11, 15]
def test1_target : Int := 9
def test1_Expected : Array Nat := #[1, 2]

-- Test case 2: Example 2
-- numbers = [2,3,4], target = 6 => [1,3]
def test2_numbers : Array Int := #[2, 3, 4]
def test2_target : Int := 6
def test2_Expected : Array Nat := #[1, 3]

-- Test case 3: Example 3 (includes negative)
-- numbers = [-1,0], target = -1 => [1,2]
def test3_numbers : Array Int := #[-1, 0]
def test3_target : Int := -1
def test3_Expected : Array Nat := #[1, 2]

-- Test case 4: Contains duplicates, unique solution uses equal values
-- numbers = [1,1,3,4], target = 2 => [1,2]
def test4_numbers : Array Int := #[1, 1, 3, 4]
def test4_target : Int := 2
def test4_Expected : Array Nat := #[1, 2]

-- Test case 5: Duplicates but solution uses farthest pair
-- numbers = [0,0,3,4], target = 4 => [1,4]
def test5_numbers : Array Int := #[0, 0, 3, 4]
def test5_target : Int := 4
def test5_Expected : Array Nat := #[1, 4]

-- Test case 6: All negative, minimal size 2
-- numbers = [-5,-2], target = -7 => [1,2]
def test6_numbers : Array Int := #[-5, -2]
def test6_target : Int := -7
def test6_Expected : Array Nat := #[1, 2]

-- Test case 7: Larger array, solution in the middle
-- numbers = [-10,-3,0,5,9,12], target = 6 => [-3 + 9]
-- indices 2 and 5 (1-based)
def test7_numbers : Array Int := #[-10, -3, 0, 5, 9, 12]
def test7_target : Int := 6
def test7_Expected : Array Nat := #[2, 5]

-- Test case 8: Boundary-ish: uses first and last elements
-- numbers = [1,2,3,4,10], target = 11 => [1,5]
def test8_numbers : Array Int := #[1, 2, 3, 4, 10]
def test8_target : Int := 11
def test8_Expected : Array Nat := #[1, 5]

-- Test case 9: Includes many equal elements, unique solution still exists
-- numbers = [2,2,2,2,9], target = 11 => [1,5]
def test9_numbers : Array Int := #[2, 2, 2, 2, 9]
def test9_target : Int := 11
def test9_Expected : Array Nat := #[1, 5]
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((TwoSumIISorted test1_numbers test1_target).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((TwoSumIISorted test2_numbers test2_target).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((TwoSumIISorted test3_numbers test3_target).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((TwoSumIISorted test4_numbers test4_target).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((TwoSumIISorted test5_numbers test5_target).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((TwoSumIISorted test6_numbers test6_target).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((TwoSumIISorted test7_numbers test7_target).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((TwoSumIISorted test8_numbers test8_target).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((TwoSumIISorted test9_numbers test9_target).run), DivM.res test9_Expected ]
end Assertions

section Pbt
-- Decidable instance synthesis failed for this method's conditions. Giving up on PBT.

-- velvet_plausible_test TwoSumIISorted (config := { maxMs := some 5000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0_0
    (numbers : Array ℤ)
    (left : ℕ)
    (right : ℕ)
    (invariant_right_bound : right < numbers.size)
    (if_pos : left < right)
    (require_1 : OfNat.ofNat 2 ≤ numbers.size ∧
  (∀ (i j : ℕ), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!) ∧
    (∃ i j, i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = numbers[left]! + numbers[right]!) ∧
      ∀ (i₁ j₁ i₂ j₂ : ℕ),
        i₁ < j₁ →
          j₁ < numbers.size →
            numbers[i₁]! + numbers[j₁]! = numbers[left]! + numbers[right]! →
              i₂ < j₂ →
                j₂ < numbers.size → numbers[i₂]! + numbers[j₂]! = numbers[left]! + numbers[right]! → i₁ = i₂ ∧ j₁ = j₂)
    : postcondition numbers (numbers[left]! + numbers[right]!) #[left + OfNat.ofNat 1, right + OfNat.ofNat 1] := by
    unfold postcondition outputMatchesUniquePair
    have huniq := require_1.2.2.2
    have h_getelem0 : (#[left + 1, right + 1] : Array ℕ)[0]! = left + 1 := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?]
    have h_getelem1 : (#[left + 1, right + 1] : Array ℕ)[1]! = right + 1 := by
      simp [Array.getElem!_eq_getD, Array.getD_getElem?]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · -- 1 ≤ result[0]!
      rw [h_getelem0]; omega
    · -- result[0]! < result[1]!
      rw [h_getelem0, h_getelem1]; omega
    · -- result[1]! ≤ numbers.size
      rw [h_getelem1]; omega
    · -- numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target
      rw [h_getelem0, h_getelem1]
      simp
    · -- uniqueness
      intro i j hij
      unfold isWitnessPair at hij
      obtain ⟨hij_lt, hj_bound, hsum⟩ := hij
      have hleft_right := huniq left right i j if_pos invariant_right_bound rfl hij_lt hj_bound hsum
      rw [h_getelem0, h_getelem1]
      omega

theorem goal_0
    (numbers : Array ℤ)
    (left : ℕ)
    (right : ℕ)
    (invariant_right_bound : right < numbers.size)
    (if_pos : left < right)
    (require_1 : OfNat.ofNat 2 ≤ numbers.size ∧ (∀ (i j : ℕ), i < j → j < numbers.size → numbers[i]! ≤ numbers[j]!) ∧ (∃ i j, i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = numbers[left]! + numbers[right]!) ∧ ∀ (i₁ j₁ i₂ j₂ : ℕ), i₁ < j₁ → j₁ < numbers.size → numbers[i₁]! + numbers[j₁]! = numbers[left]! + numbers[right]! → i₂ < j₂ → j₂ < numbers.size → numbers[i₂]! + numbers[j₂]! = numbers[left]! + numbers[right]! → i₁ = i₂ ∧ j₁ = j₂)
    : ∀ (i j : ℕ), i < j → j < numbers.size → numbers[i]! + numbers[j]! = numbers[left]! + numbers[right]! → right ≤ i ∧ j ≤ right ∨ postcondition numbers (numbers[left]! + numbers[right]!) #[left + OfNat.ofNat 1, right + OfNat.ofNat 1] := by
    have h_post : postcondition numbers (numbers[left]! + numbers[right]!) #[left + OfNat.ofNat 1, right + OfNat.ofNat 1] := by expose_names; exact (goal_0_0 numbers left right invariant_right_bound if_pos require_1)
    intro i j hij hjsz hsum
    exact Or.inr h_post

set_option loom.solver "custom"

macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try injections
  try subst_vars
  try grind (gen := 4)))


prove_correct TwoSumIISorted by
  loom_solve <;> (try injections; try subst_vars; try (simp [-postcondition] at *); try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 numbers left right invariant_right_bound if_pos require_1)
end Proof
