/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 30d4ad6e-2c31-4005-92dc-50f95a66083b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal (numbers : Array Int) (target : Int) (h_precond : precondition numbers target) : postcondition numbers target (implementation numbers target)
-/

import Lean

import Mathlib.Tactic


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
  let n := numbers.size
  -- two-pointer recursion: i from left, j from right
  let rec go (i j : Nat) : Array Nat :=
    if hlt : i < j then
      let s := numbers[i]! + numbers[j]!
      if s == target then
        #[i + 1, j + 1]
      else if s < target then
        go (i + 1) j
      else
        go i (j - 1)
    else
      -- Unreachable under the stated precondition (unique solution exists).
      #[0, 0]
  if h : 0 < n then
    go 0 (n - 1)
  else
    -- Unreachable under the stated precondition (n ≥ 2).
    #[0, 0]

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

section Proof

theorem correctness_goal (numbers : Array Int) (target : Int) (h_precond : precondition numbers target) : postcondition numbers target (implementation numbers target) := by
    obtain ⟨ h_unique, h_exists ⟩ := h_precond;
    -- By definition of `hasUniqueWitnessPair`, there exists a unique pair `(i, j)` such that `i < j`, `j < numbers.size`, and `numbers[i]! + numbers[j]! = target`.
    obtain ⟨i, j, h_pair⟩ : ∃ i j, i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target ∧ ∀ i' j', i' < j' → j' < numbers.size → numbers[i']! + numbers[j']! = target → i' = i ∧ j' = j := by
      obtain ⟨ i, j, h ⟩ := h_exists.2.1;
      exact ⟨ i, j, h.1, h.2.1, h.2.2, fun i' j' hi' hj' hsum => h_exists.2.2 i' j' i j ⟨ hi', hj', hsum ⟩ ⟨ h.1, h.2.1, h.2.2 ⟩ ⟩;
    -- By definition of `implementation`, we know that it will return the indices of the unique pair `(i, j)` such that `i < j`, `j < numbers.size`, and `numbers[i]! + numbers[j]! = target`. We will prove this by induction on the size of the array.
    have h_ind : ∀ (i' j' : ℕ), i' ≤ i → j' ≥ j → i' < j' → j' < numbers.size → (implementation.go numbers target i' j') = #[i + 1, j + 1] := by
      intros i' j' hi' hj' hij' hj'_lt_size
      induction' h : j' - i' using Nat.strong_induction_on with k ih generalizing i' j';
      unfold implementation.go;
      split_ifs ; norm_num at *;
      split_ifs;
      · grind;
      · by_cases hi'' : i' + 1 ≤ i;
        · exact ih _ ( by omega ) _ _ ( by omega ) ( by omega ) ( by omega ) ( by omega ) rfl;
        · norm_num [ show i' = i by linarith ] at *;
          contrapose! h_pair;
          intro hij hj_lt_size h_eq;
          use i, j';
          exact ⟨ hij', hj'_lt_size, by linarith [ h_exists.1 i j hij hj_lt_size, h_exists.1 j j' ( lt_of_le_of_ne hj' ( Ne.symm <| by aesop ) ) hj'_lt_size ], fun _ => by aesop ⟩;
      · by_cases h_cases : j' - 1 < j;
        · norm_num [ show j' = j by omega ] at *;
          -- Since $i' \leq i$ and $i < j$, we have $numbers[i']! \leq numbers[i]!$ by the non-decreasing property of the array.
          have h_le : numbers[i']! ≤ numbers[i]! := by
            by_cases hi'' : i' < i;
            · exact h_exists.1 _ _ hi'' ( by linarith );
            · grind;
          omega;
        · exact ih _ ( by omega ) _ _ hi' ( by omega ) ( by omega ) ( by omega ) rfl;
    unfold implementation;
    -- Apply the induction hypothesis with i' = 0 and j' = numbers.size - 1.
    have h_apply_ind : implementation.go numbers target 0 (numbers.size - 1) = #[i + 1, j + 1] := by
      exact h_ind 0 ( numbers.size - 1 ) ( Nat.zero_le _ ) ( Nat.le_sub_one_of_lt h_pair.2.1 ) ( by omega ) ( Nat.sub_lt ( by linarith ) ( by linarith ) );
    simp +zetaDelta at *;
    rw [ if_pos ( by linarith ), h_apply_ind ];
    constructor <;> norm_num;
    exact ⟨ h_pair.1, by linarith, h_pair.2.2.1, fun i' j' hij => by have := h_pair.2.2.2 i' j' hij.1 hij.2.1 hij.2.2; tauto ⟩

end Proof