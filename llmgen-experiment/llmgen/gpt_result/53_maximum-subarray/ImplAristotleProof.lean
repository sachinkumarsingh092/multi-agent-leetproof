/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 949d3621-3dd2-4e7c-ba74-54514e79701e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem goal_10 (nums : Array ℤ) (bestEndingHere : ℤ) (bestSoFar : ℤ) (i : ℕ) (a : OfNat.ofNat 1 ≤ i) (a_1 : i ≤ nums.size) (if_pos : i < nums.size) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere) (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere) (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar) (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar) (if_neg : OfNat.ofNat 0 < bestEndingHere) (if_pos_1 : bestSoFar < bestEndingHere + nums[i]!) : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestEndingHere + nums[i]!

- theorem goal_13 (nums : Array ℤ) (bestEndingHere : ℤ) (bestSoFar : ℤ) (i : ℕ) (a : OfNat.ofNat 1 ≤ i) (a_1 : i ≤ nums.size) (if_pos : i < nums.size) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere) (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere) (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar) (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar) (if_neg : OfNat.ofNat 0 < bestEndingHere) (if_neg_1 : bestEndingHere + nums[i]! ≤ bestSoFar) : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar

- theorem goal_14 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) = nums[OfNat.ofNat 0]!

- theorem goal_15 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) ≤ nums[OfNat.ofNat 0]!

- theorem goal_16 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : ∃ start stop, start < stop ∧ stop ≤ OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = nums[OfNat.ofNat 0]!

- theorem goal_17 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : ∀ (start stop : ℕ), start < stop → stop ≤ OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ nums[OfNat.ofNat 0]!
-/

import Mathlib.Tactic


-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    MaximumSubarray: return the maximum possible sum of a non-empty contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A contiguous subarray is determined by indices `start` and `stop` with `start < stop`.
    3. The sum of a subarray is the sum of the elements in `nums[start:stop]`.
    4. The result is the sum of some non-empty contiguous subarray (achievability).
    5. The result is greater than or equal to the sum of every non-empty contiguous subarray (maximality).
    6. The input must be non-empty so that at least one non-empty subarray exists.
-/

section Specs

-- Sum of all elements in an array.
def arraySum (arr : Array Int) : Int :=
  arr.foldl (fun acc x => acc + x) 0

-- Sum of the contiguous segment nums[start:stop].
-- This uses Array.extract; the spec restricts start/stop so no clamping occurs.
def rangeSum (nums : Array Int) (start : Nat) (stop : Nat) : Int :=
  arraySum (nums.extract start stop)

-- Input must be non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- result is the maximum sum among all non-empty contiguous subarrays.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size ∧ rangeSum nums start stop = result) ∧
  (∀ (start : Nat) (stop : Nat),
      start < stop ∧ stop ≤ nums.size → rangeSum nums start stop ≤ result)

end Specs

section TestCases

-- Test case 1: Example 1
-- nums = [-2,1,-3,4,-1,2,1,-5,4] => 6 (subarray [4,-1,2,1])
def test1_nums : Array Int := #[-2, 1, -3, 4, -1, 2, 1, -5, 4]

def test1_Expected : Int := 6

-- Test case 2: Example 2 (single element)
def test2_nums : Array Int := #[1]

def test2_Expected : Int := 1

-- Test case 3: Example 3 (whole array is best)
def test3_nums : Array Int := #[5, 4, -1, 7, 8]

def test3_Expected : Int := 23

-- Test case 4: All negative (best is the least negative single element)
def test4_nums : Array Int := #[-8, -3, -6, -2, -5, -4]

def test4_Expected : Int := -2

-- Test case 5: Contains zeros; best is 0 (choose [0])
def test5_nums : Array Int := #[0, -1, 0, -2]

def test5_Expected : Int := 0

-- Test case 6: Mixed, best is a suffix/prefix segment
-- Best subarray is [3, -1, 2] with sum 4

def test6_nums : Array Int := #[-2, 3, -1, 2, -1]

def test6_Expected : Int := 4

-- Test case 7: Alternating small values
-- Best subarray is [1, -1, 1, -1, 1] has max 1 (any single 1)
def test7_nums : Array Int := #[1, -1, 1, -1, 1]

def test7_Expected : Int := 1

-- Test case 8: Best is the entire array

def test8_nums : Array Int := #[2, 3, 1]

def test8_Expected : Int := 6

-- Test case 9: Two elements, decreasing
-- Best is [10] not [10,-20]
def test9_nums : Array Int := #[10, -20]

def test9_Expected : Int := 10

end TestCases

section Proof

theorem goal_10 (nums : Array ℤ) (bestEndingHere : ℤ) (bestSoFar : ℤ) (i : ℕ) (a : OfNat.ofNat 1 ≤ i) (a_1 : i ≤ nums.size) (if_pos : i < nums.size) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere) (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere) (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar) (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar) (if_neg : OfNat.ofNat 0 < bestEndingHere) (if_pos_1 : bestSoFar < bestEndingHere + nums[i]!) : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestEndingHere + nums[i]! := by
    intros start stop hstart hstop;
    by_cases hstart' : start < i;
    · cases hstop.eq_or_lt <;> simp_all +decide [ Nat.lt_succ_iff ];
      · rw [ show nums.extract start ( i + 1 ) = nums.extract start i ++ #[nums[i]!] from ?_ ];
        · simp +zetaDelta at *;
          convert add_le_add ( invariant_inv_ending_max start hstart' ) le_rfl using 1;
          grind;
        · refine' Array.ext _ _ <;> aesop;
      · grind +ring;
    · cases hstop.eq_or_lt <;> simp_all +decide [ Nat.succ_eq_add_one ];
      · norm_num [ show start = i by linarith ];
        simp +decide [ Array.extract, if_pos ];
        simp +decide [ Array.extract.loop, min_eq_left ( by linarith : i + 1 ≤ nums.size ) ];
        split_ifs ; norm_num ; linarith;
      · grind +ring

theorem goal_13 (nums : Array ℤ) (bestEndingHere : ℤ) (bestSoFar : ℤ) (i : ℕ) (a : OfNat.ofNat 1 ≤ i) (a_1 : i ≤ nums.size) (if_pos : i < nums.size) (require_1 : OfNat.ofNat 0 < nums.size) (invariant_inv_ending_ex : ∃ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) = bestEndingHere) (invariant_inv_ending_max : ∀ start < i, Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start i) (OfNat.ofNat 0) (min i nums.size - start) ≤ bestEndingHere) (invariant_inv_sofar_ex : ∃ start stop, start < stop ∧ stop ≤ i ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = bestSoFar) (invariant_inv_sofar_max : ∀ (start stop : ℕ), start < stop → stop ≤ i → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar) (if_neg : OfNat.ofNat 0 < bestEndingHere) (if_neg_1 : bestEndingHere + nums[i]! ≤ bestSoFar) : ∀ (start stop : ℕ), start < stop → stop ≤ i + OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ bestSoFar := by
    -- If stop is exactly i+1, then the sum would be the sum up to i plus nums[i]!. But since bestEndingHere is the maximum sum ending at i, and bestSoFar is the maximum so far, adding nums[i]! to bestEndingHere should still be less than or equal to bestSoFar.
    intros start stop hstart hstop
    by_cases hstop_eq : stop = i + 1;
    · by_cases hstart_eq : start = i <;> simp_all +decide [ Nat.succ_le_iff ];
      · -- Since the subarray from i to i+1 is just the element at i, its sum is nums[i]!.
        have h_sum : Array.foldl (fun (acc x : ℤ) => acc + x) 0 (nums.extract i (i + 1)) = nums[i]! := by
          simp +decide [ Array.extract, if_pos ];
          simp +decide [ Array.extract.loop, if_pos, Nat.succ_eq_add_one, min_eq_left ( by linarith : i + 1 ≤ nums.size ) ];
        convert h_sum.le.trans _;
        · simp +arith +decide [ if_pos ];
          grind;
        · grind +ring;
      · cases lt_or_gt_of_ne hstart_eq <;> simp_all +decide [ Nat.succ_eq_add_one ];
        · rw [ show nums.extract start ( i + 1 ) = nums.extract start i ++ #[nums[i]!] from ?_ ];
          · simp +zetaDelta at *;
            convert le_trans _ if_neg_1 using 1;
            convert add_le_add ( invariant_inv_ending_max start ‹_› ) le_rfl using 1;
            grind;
          · simp +decide [ Array.ext_iff, * ];
            simp +decide [ *, min_eq_left ( by linarith : start ≤ i ) ];
        · grind +ring;
    · exact invariant_inv_sofar_max start stop hstart ( Nat.le_of_lt_succ ( lt_of_le_of_ne hstop hstop_eq ) )

theorem goal_14 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) = nums[OfNat.ofNat 0]! := by
    rcases nums with ⟨ ⟨ l ⟩ ⟩ <;> aesop;

theorem goal_15 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (OfNat.ofNat 1)) (OfNat.ofNat 0) (min (OfNat.ofNat 1) nums.size) ≤ nums[OfNat.ofNat 0]! := by
    rcases nums with ⟨ ⟨ l ⟩ ⟩ <;> aesop

theorem goal_16 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : ∃ start stop, start < stop ∧ stop ≤ OfNat.ofNat 1 ∧ Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) = nums[OfNat.ofNat 0]! := by
    rcases nums with ⟨ ⟨ ⟩ ⟩ <;> aesop

theorem goal_17 (nums : Array ℤ) (require_1 : OfNat.ofNat 0 < nums.size) : ∀ (start stop : ℕ), start < stop → stop ≤ OfNat.ofNat 1 → Array.foldl (fun acc x => acc + x) (OfNat.ofNat 0) (nums.extract start stop) (OfNat.ofNat 0) (min stop nums.size - start) ≤ nums[OfNat.ofNat 0]! := by
    -- Since the array is non-empty, the only possible subarray here is the array itself. So the sum is just the element at index 0.
    intros start stop hstart hstop
    have h_subarray : start = 0 ∧ stop = 1 := by
      -- Since start is a natural number and start < stop, the only possibility is start = 0.
      have h_start_zero : start = 0 := by
        exact Nat.eq_zero_of_le_zero ( Nat.le_of_lt_succ ( lt_of_lt_of_le hstart hstop ) );
      exact ⟨ h_start_zero, le_antisymm hstop ( by simpa [ h_start_zero ] using hstart ) ⟩;
    rcases nums with ⟨ ⟨ l ⟩ ⟩ <;> aesop

end Proof