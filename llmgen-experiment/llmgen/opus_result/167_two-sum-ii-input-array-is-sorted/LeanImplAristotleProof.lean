/- This file type checks in Lean 4.28 -/

import Lean

import Mathlib

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

section Proof

/-
PROVIDED SOLUTION
By induction on `fuel`.

**Base case (fuel = 0):** We have `fuel ≥ right - left`, so `right - left = 0`, meaning `right ≤ left`. But from the witness pair, `i_star < j_star` (from `isWitnessPair`), and `left ≤ i_star < j_star ≤ right ≤ left`, which is a contradiction with `left ≤ right` (actually `left = right` but `i_star < j_star` with `left ≤ i_star` and `j_star ≤ right = left` gives `j_star ≤ i_star`, contradicting `i_star < j_star`).

**Inductive case (fuel = fuel' + 1):** Unfold `twoPointer`. We know `left ≤ right` (given) and `right < numbers.size` (given).

Let `sum = numbers[left]! + numbers[right]!`.

Case 1: `sum = target`. The function returns `#[left + 1, right + 1]`. We need `left = i_star` and `right = j_star`. Since `left < right` (we have `left ≤ i_star < j_star ≤ right` so `left < right` or `left = right`, but the latter gives contradiction as in base case, so `left < right`), and `right < numbers.size`, the pair `(left, right)` is a witness pair. By uniqueness (`h_uniq`), `left = i_star` and `right = j_star`.

Wait, but we need `left < right`. We have `left ≤ i_star < j_star ≤ right`. If `left = right` then `i_star < j_star ≤ left = right` and `left ≤ i_star`, so `i_star = left = right` and `j_star ≤ right = i_star`, contradicting `i_star < j_star`. So `left < right`.

Also need to handle the `if left < right` branch. Since `left < right`, we enter the branch. Since `right < numbers.size`, we enter the inner branch. Then we check the sum.

For `sum == target` (BEq on Int): `sum == target` iff `sum = target` for Int. So we return `#[left+1, right+1]` and need `left = i_star ∧ right = j_star`. Since `(left, right)` is a witness pair (left < right, right < numbers.size, sum = target), by uniqueness, done.

Case 2: `sum < target`. Then the function recurses with `(left + 1, right, fuel')`. We apply IH. Need:
- `left + 1 ≤ i_star`: If `left = i_star`, then `numbers[i_star]! + numbers[right]! < target = numbers[i_star]! + numbers[j_star]!`, so `numbers[right]! < numbers[j_star]!`. But `j_star ≤ right` and sorted gives `numbers[j_star]! ≤ numbers[right]!`, contradiction. So `left < i_star`, i.e., `left + 1 ≤ i_star`.
- `j_star ≤ right`: already given.
- `left + 1 ≤ right`: `left < right` so `left + 1 ≤ right`.
- `right < numbers.size`: given.
- `fuel' ≥ right - (left + 1)`: `fuel = fuel' + 1 ≥ right - left`, so `fuel' ≥ right - left - 1 = right - (left + 1)`.

Case 3: `sum > target` (the else branch, i.e., `¬(sum == target)` and `¬(sum < target)`, so `sum > target`). Recurse with `(left, right - 1, fuel')`. Apply IH:
- `left ≤ i_star`: given.
- `j_star ≤ right - 1`: If `right = j_star`, then `numbers[left]! + numbers[j_star]! > target = numbers[i_star]! + numbers[j_star]!`, so `numbers[left]! > numbers[i_star]!`. But `left ≤ i_star` and sorted gives `numbers[left]! ≤ numbers[i_star]!`, contradiction. So `j_star < right`, i.e., `j_star ≤ right - 1`.
- `left ≤ right - 1`: `left < right` so `left ≤ right - 1`.
- `right - 1 < numbers.size`: `right < numbers.size` so `right - 1 < numbers.size`.
- `fuel' ≥ (right - 1) - left`: `fuel' + 1 ≥ right - left`, so `fuel' ≥ right - left - 1 = (right - 1) - left`.

Key observations for the proof:
- Use `h_sorted` (isSortedNondecreasing) to derive monotonicity: `i ≤ j → j < size → numbers[i]! ≤ numbers[j]!`
- Use `h_uniq` for uniqueness of witness pairs
- The `BEq` instance for `Int` is decidable equality, so `sum == target` is `decide (sum = target)`
- Be careful with Nat subtraction (truncating): `right - left` in Nat, `fuel ≥ right - left`
- `isWitnessPair` unfolds to `i < j ∧ j < numbers.size ∧ numbers[i]! + numbers[j]! = target`

The proof structure: `intro left right fuel h_left h_right h_lr h_rs h_fuel; induction fuel generalizing left right` then case split.
-/
theorem correctness_goal_0 (numbers : Array ℤ) (target : ℤ) (h_size : numbers.size ≥ 2) (h_sorted : isSortedNondecreasing numbers) (h_uniq : ∀ (i₁ j₁ i₂ j₂ : ℕ), isWitnessPair numbers target i₁ j₁ → isWitnessPair numbers target i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂) (i_star : ℕ) (j_star : ℕ) (h_witness : isWitnessPair numbers target i_star j_star) : ∀ (left right fuel : ℕ),
  left ≤ i_star →
    j_star ≤ right →
      left ≤ right →
        right < numbers.size →
          fuel ≥ right - left → implementation.twoPointer numbers target left right fuel = #[i_star + 1, j_star + 1] := by
    intros left right fuel h_left h_right h_lr h_rs h_fuel
    induction' fuel with fuel ih generalizing left right;
    · norm_num +zetaDelta at *;
      rw [ Nat.sub_eq_iff_eq_add ] at h_fuel <;> linarith [ h_witness.1 ];
    · by_cases h_sum : numbers[left]! + numbers[right]! = target;
      · -- Since `left ≤ i_star` and `j_star ≤ right`, and `right < numbers.size`, the pair `(left, right)` is a witness pair.
        have h_witness_pair : isWitnessPair numbers target left right := by
          exact ⟨ lt_of_le_of_ne h_lr ( by rintro rfl; linarith [ h_witness.1, h_witness.2 ] ), h_rs, h_sum ⟩;
        specialize h_uniq left right i_star j_star h_witness_pair h_witness;
        unfold implementation.twoPointer; aesop;
      · by_cases h_sum_lt : numbers[left]! + numbers[right]! < target;
        · -- Since `left < i_star`, we have `left + 1 ≤ i_star`.
          have h_left_plus_one : left + 1 ≤ i_star := by
            contrapose! h_sum_lt;
            norm_num [ show i_star = left by linarith ] at *;
            linarith [ h_witness.2.2, show numbers[j_star]! ≤ numbers[right]! from h_sorted _ _ ( lt_of_le_of_ne h_right ( Ne.symm <| by rintro rfl; exact h_sum <| by linarith [ h_witness.2.2 ] ) ) h_rs ];
          rw [ show implementation.twoPointer numbers target left right ( fuel + 1 ) = implementation.twoPointer numbers target ( left + 1 ) right fuel from ?_ ];
          · apply ih;
            · linarith;
            · linarith;
            · linarith [ h_witness.1 ];
            · linarith;
            · omega;
          · rw [ implementation.twoPointer ];
            split_ifs <;> norm_num at *;
            · rw [ if_neg h_sum, if_pos h_sum_lt ];
            · linarith [ h_witness.1 ];
        · convert ih left ( right - 1 ) h_left _ _ _ _ using 1;
          · rw [ implementation.twoPointer ];
            split_ifs <;> norm_num at *;
            · rw [ if_neg h_sum, if_neg ( not_lt_of_ge h_sum_lt ) ];
            · cases ‹_› ; simp_all +decide [ isWitnessPair ];
              · grind;
              · grind;
          · refine Nat.le_sub_one_of_lt <| lt_of_le_of_ne h_right ?_;
            rintro rfl;
            exact h_sum ( by linarith [ h_witness.2.2, show numbers[left]! ≤ numbers[i_star]! from h_sorted _ _ ( lt_of_le_of_ne h_left ( Ne.symm <| by rintro rfl; exact h_sum <| by linarith [ h_witness.2.2 ] ) ) ( by linarith [ h_witness.1 ] ) ] );
          · contrapose! h_sum;
            norm_num [ show left = right by omega ] at *;
            linarith [ h_witness.2, h_witness.1, h_sorted _ _ ( show i_star < j_star from h_witness.1 ) ( by linarith ) ];
          · omega;
          · omega

end Proof
