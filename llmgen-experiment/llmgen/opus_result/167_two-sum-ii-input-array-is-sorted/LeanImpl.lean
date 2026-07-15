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
def implementation (numbers : Array Int) (target : Int) : Array Nat :=
  let rec twoPointer (left right : Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => #[left + 1, right + 1]
    | fuel' + 1 =>
      if h1 : left < right then
        if h2 : right < numbers.size then
          let sum := numbers[left]! + numbers[right]!
          if sum == target then
            #[left + 1, right + 1]
          else if sum < target then
            twoPointer (left + 1) right fuel'
          else
            twoPointer left (right - 1) fuel'
        else
          #[left + 1, right + 1]
      else
        #[left + 1, right + 1]
  if numbers.size < 2 then #[0, 0]
  else twoPointer 0 (numbers.size - 1) numbers.size
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
#assert_same_evaluation #[(implementation test1_numbers test1_target), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_numbers test2_target), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_numbers test3_target), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_numbers test4_target), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_numbers test5_target), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_numbers test6_target), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_numbers test7_target), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_numbers test8_target), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_numbers test9_target), test9_Expected]
end Assertions

section Pbt
-- Lean wrapper for velvet_plausible_test failed to compile. Giving up on PBT.

-- method implementationPbt (numbers : Array Int) (target : Int)
--   return (result : Array Nat)
--   require precondition numbers target
--   ensures postcondition numbers target result
--   do
--   return (implementation numbers target)

-- velvet_plausible_test implementationPbt (config := { maxMs := some 5000 })
end Pbt

section Proof
theorem correctness_goal_0
    (numbers : Array ℤ)
    (target : ℤ)
    (h_size : numbers.size ≥ 2)
    (h_sorted : isSortedNondecreasing numbers)
    (h_uniq : ∀ (i₁ j₁ i₂ j₂ : ℕ), isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)
    (i_star : ℕ)
    (j_star : ℕ)
    (h_witness : isWitnessPair numbers target i_star j_star)
    : ∀ (left right fuel : ℕ),
  left ≤ i_star →
    j_star ≤ right →
      left ≤ right →
        right < numbers.size →
          fuel ≥ right - left → implementation.twoPointer numbers target left right fuel = #[i_star + 1, j_star + 1] := by
    sorry

theorem correctness_goal_1
    (numbers : Array ℤ)
    (target : ℤ)
    (h_uniq : ∀ (i₁ j₁ i₂ j₂ : ℕ), isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂)
    (i_star : ℕ)
    (j_star : ℕ)
    (h_witness : isWitnessPair numbers target i_star j_star)
    : postcondition numbers target #[i_star + 1, j_star + 1] := by
    unfold postcondition outputMatchesUniquePair
    have h_ij := h_witness.1
    have h_jsize := h_witness.2.1
    have h_sum := h_witness.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- size = 2
      simp
    · -- 1 ≤ result[0]!
      simp
    · -- result[0]! < result[1]!
      simp
      omega
    · -- result[1]! ≤ numbers.size
      simp
      omega
    · -- numbers[(result[0]! - 1)]! + numbers[(result[1]! - 1)]! = target
      simp
      exact h_sum
    · -- uniqueness
      intro i j h_ij_witness
      have h_eq := h_uniq i_star j_star i j h_witness h_ij_witness
      simp
      exact h_eq


theorem correctness_goal
    (numbers : Array Int)
    (target : Int)
    (h_precond : precondition numbers target)
    : postcondition numbers target (implementation numbers target) := by
    unfold precondition at h_precond
    obtain ⟨h_size, h_sorted, h_unique⟩ := h_precond
    unfold hasUniqueWitnessPair at h_unique
    obtain ⟨⟨i_star, j_star, h_witness⟩, h_uniq⟩ := h_unique
    -- Main loop invariant lemma
    have h_loop : ∀ (left right fuel : Nat),
      left ≤ i_star → j_star ≤ right → left ≤ right → right < numbers.size →
      fuel ≥ right - left →
      implementation.twoPointer numbers target left right fuel = #[i_star + 1, j_star + 1] := by expose_names; exact (correctness_goal_0 numbers target h_size h_sorted h_uniq i_star j_star h_witness)
    -- The implementation enters the loop with correct initial values
    have h_init_right : j_star ≤ numbers.size - 1 := by
      unfold isWitnessPair at h_witness; omega
    have h_impl_eq : implementation numbers target = #[i_star + 1, j_star + 1] := by
      unfold implementation
      have : ¬ (numbers.size < 2) := by omega
      split
      · omega
      · exact h_loop 0 (numbers.size - 1) numbers.size (Nat.zero_le i_star) h_init_right (by omega) (by omega) (by omega)
    -- Now prove the postcondition from h_impl_eq
    have h_post : postcondition numbers target #[i_star + 1, j_star + 1] := by expose_names; exact (correctness_goal_1 numbers target h_uniq i_star j_star h_witness)
    rw [h_impl_eq]
    exact h_post
end Proof
