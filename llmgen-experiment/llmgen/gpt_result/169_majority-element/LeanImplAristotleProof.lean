/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0d6f0ef3-9e0e-4147-b7b3-b797cfd374db

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal (nums : Array Int) (h_precond : precondition nums) : postcondition nums (implementation nums)
-/

import Lean

import Mathlib.Tactic


set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    169. Majority Element: Return the array element that appears strictly more than ⌊n/2⌋ times.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array `nums` of length `n`.
    2. For a value `x`, its frequency is the number of indices whose element equals `x`.
    3. A value `x` is a majority element if its frequency is strictly greater than ⌊n/2⌋.
    4. The problem guarantees that at least one majority element exists.
    5. The output must be a value that is a majority element of `nums`.
    6. Such a majority element is unique: if any value has frequency > ⌊n/2⌋, it must equal the output.
-/

-- Helper: the majority threshold (⌊n/2⌋).
-- Using Nat division, since Array.size and Array.count are Nat.
def majorityThreshold (n : Nat) : Nat :=
  n / 2

-- Helper predicate: `x` is a majority element of `nums`.
def isMajority (nums : Array Int) (x : Int) : Prop :=
  nums.count x > majorityThreshold nums.size

-- Preconditions
-- The problem states a majority element always exists.
def precondition (nums : Array Int) : Prop :=
  ∃ x : Int, isMajority nums x

-- Postconditions
-- The returned value is the unique majority element.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  isMajority nums result ∧
  (∀ y : Int, isMajority nums y → y = result)

end Specs

section Impl

def implementation (nums : Array Int) : Int :=
  -- Boyer–Moore majority vote algorithm (single pass, O(1) extra space)
  let step : (Option Int × Int) → Int → (Option Int × Int) :=
    fun state x =>
      match state with
      | (none, _) => (some x, 1)
      | (some cand, cnt) =>
          if cnt == 0 then
            (some x, 1)
          else if x == cand then
            (some cand, cnt + 1)
          else
            (some cand, cnt - 1)
  let (candOpt, _) := nums.foldl step (none, 0)
  -- Under the precondition, there is a majority element, hence candidate exists.
  match candOpt with
  | some c => c
  | none => 0

end Impl

section TestCases

-- Test case 1: Example 1
-- Input: [3,2,3] -> majority is 3
-- counts: 3 appears 2 times, n=3, ⌊n/2⌋=1

def test1_nums : Array Int := #[3, 2, 3]

def test1_Expected : Int := 3

-- Test case 2: Example 2
-- Input: [2,2,1,1,1,2,2] -> majority is 2

def test2_nums : Array Int := #[2, 2, 1, 1, 1, 2, 2]

def test2_Expected : Int := 2

-- Test case 3: Single element (smallest valid n)

def test3_nums : Array Int := #[5]

def test3_Expected : Int := 5

-- Test case 4: Two elements, both same

def test4_nums : Array Int := #[7, 7]

def test4_Expected : Int := 7

-- Test case 5: Majority is 0, includes 0 boundary value

def test5_nums : Array Int := #[0, 1, 0]

def test5_Expected : Int := 0

-- Test case 6: Majority is negative number

def test6_nums : Array Int := #[-1, -1, 2]

def test6_Expected : Int := -1

-- Test case 7: Larger odd length, clear majority

def test7_nums : Array Int := #[9, 9, 9, 1, 2]

def test7_Expected : Int := 9

-- Test case 8: Larger even length, majority just above n/2
-- n=6, threshold=3, so majority count must be >=4

def test8_nums : Array Int := #[1, 2, 2, 2, 2, 3]

def test8_Expected : Int := 2

-- Test case 9: Majority appears many times, other values mixed

def test9_nums : Array Int := #[4, 4, 4, 4, 4, 2, 3, 4, 1]

def test9_Expected : Int := 4

end TestCases

section Proof

noncomputable section AristotleLemmas

/-
Helper definitions and correctness theorem for the Boyer-Moore majority vote algorithm.
`boyerMooreStep` is the step function.
`boyerMooreInvariant` relates the count of the majority element to the current candidate and counter.
`boyerMoore_correct` proves that if a majority element exists, the algorithm returns it.
-/
section BoyerMooreHelpers

def boyerMooreStep (state : Option Int × Int) (x : Int) : Option Int × Int :=
  match state with
  | (none, _) => (some x, 1)
  | (some cand, cnt) =>
      if cnt == 0 then
        (some x, 1)
      else if x == cand then
        (some cand, cnt + 1)
      else
        (some cand, cnt - 1)

def boyerMooreInvariant (m : Int) (processed : List Int) (state : Option Int × Int) : Prop :=
  let (cand, k) := state
  k ≥ 0 ∧
  2 * (processed.count m : Int) ≤ (processed.length : Int) + (if cand == some m then k else -k)

theorem boyerMoore_correct (nums : List Int) (m : Int) (hm : 2 * (nums.count m : Int) > nums.length) :
  (nums.foldl boyerMooreStep (none, 0)).1 = some m := by
    -- By induction on the list, we can show that the invariant holds at each step.
    have h_inv : ∀ (l : List ℤ), ∀ (c : Option ℤ) (k : ℕ), 2 * (List.count m l : ℤ) + (if c = some m then (k : ℤ) else -(k : ℤ)) > l.length → (List.foldl boyerMooreStep (c, k) l).1 = some m := by
      intros l c k hk
      induction' l with x l ih generalizing c k;
      · grind;
      · rcases c with ( _ | c ) <;> simp_all +decide [ boyerMooreStep ];
        · by_cases hx : x = m <;> simp_all +decide [ List.count_cons ];
          · convert ih ( Option.some m ) 1 _ using 1 ; norm_num ; linarith;
          · convert ih ( some x ) 1 _ using 1 ; norm_num [ hx ] ; linarith;
        · convert ih _ _ _ using 2;
          rotate_left;
          exact if k = 0 then Option.some x else if x = c then Option.some c else Option.some c;
          exact if k = 0 then 1 else if x = c then k + 1 else k - 1;
          · grind;
          · cases k <;> aesop;
    simpa using h_inv nums none 0 ( by simpa using hm )

end BoyerMooreHelpers

end AristotleLemmas

theorem correctness_goal (nums : Array Int) (h_precond : precondition nums) : postcondition nums (implementation nums) := by
    obtain ⟨ m, hm ⟩ := h_precond;
    unfold postcondition isMajority at *;
    -- By definition of `implementation`, we know that it returns the majority element.
    have h_impl : (implementation nums) = m := by
      have h_impl : (nums.toList.foldl boyerMooreStep (none, 0)).fst = some m := by
        apply boyerMoore_correct;
        unfold majorityThreshold at hm; norm_num at *; omega;
      convert congr_arg Option.get! h_impl;
      unfold implementation;
      unfold boyerMooreStep; aesop;
    unfold majorityThreshold at *;
    -- By definition of `count`, we know that `Array.count y nums + Array.count m nums ≤ nums.size` for any `y ≠ m`.
    have h_count_sum : ∀ y, y ≠ m → Array.count y nums + Array.count m nums ≤ nums.size := by
      intros y hy_ne_m
      have h_count_sum : ∀ (l : List ℤ), y ≠ m → List.count y l + List.count m l ≤ l.length := by
        intros l hy_ne_m
        induction' l with x l ih;
        · norm_num;
        · grind +ring;
      simpa using h_count_sum nums.toList hy_ne_m;
    grind

end Proof