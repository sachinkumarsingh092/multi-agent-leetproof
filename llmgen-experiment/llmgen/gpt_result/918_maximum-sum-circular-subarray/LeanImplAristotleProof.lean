import Lean

import Mathlib

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option pp.funBinderTypes true

/- Problem Description
    918. Maximum Sum Circular Subarray: compute the maximum possible sum of a non-empty subarray of a circular integer array.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an integer array `nums` with length `n`.
    2. A circular subarray is determined by a start index `start` and a length `len`.
    3. The chosen elements are `nums[start], nums[(start+1) mod n], ..., nums[(start+len-1) mod n]`.
    4. The subarray must be non-empty, so `1 ≤ len`.
    5. The subarray may use each element of the underlying fixed buffer at most once, so `len ≤ n`.
    6. The output is the maximum possible sum among all valid circular subarrays.
    7. The result must be achievable by at least one valid circular subarray and must be greater than or equal to
       the sum of every valid circular subarray.
-/

-- Helper function: sum of a circular segment of length `len`, starting at index `start`.
-- Implemented as a finite sum over indices `0 .. len-1`.
-- When `arr.size > 0`, each index `(start + i) % arr.size` is within bounds.
def circSegmentSum (arr : Array Int) (start : Nat) (len : Nat) : Int :=
  (Finset.range len).sum (fun i => arr[(start + i) % arr.size]!)

-- A (start,len) pair is valid if it picks a non-empty circular segment of length at most `n`.
def isValidCircSegment (arr : Array Int) (start : Nat) (len : Nat) : Prop :=
  arr.size > 0 ∧ start < arr.size ∧ 1 ≤ len ∧ len ≤ arr.size

-- Precondition: array must be non-empty (subarray is required to be non-empty).
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- Postcondition: `result` is the maximum circular subarray sum.
-- 1) Achievability: some valid circular segment sums exactly to `result`.
-- 2) Maximality: every valid circular segment has sum ≤ result.
def postcondition (nums : Array Int) (result : Int) : Prop :=
  (∃ (start : Nat) (len : Nat),
      isValidCircSegment nums start len ∧ circSegmentSum nums start len = result) ∧
  (∀ (start : Nat) (len : Nat),
      isValidCircSegment nums start len → circSegmentSum nums start len ≤ result)
end Specs

section Impl
def implementation (nums : Array Int) : Int :=
  -- Kadane-style single pass.
  -- max circular subarray sum = max(bestMax, total - bestMin)
  -- except when all numbers are negative, where total - bestMin corresponds to empty subarray.
  if nums.size = 0 then
    0
  else
    let first : Int := nums[0]!

    let rec go (i : Nat) (total curMax bestMax curMin bestMin : Int) : Int × Int × Int :=
      if i < nums.size then
        let x : Int := nums[i]!
        let total' := total + x
        let curMax' := max x (curMax + x)
        let bestMax' := max bestMax curMax'
        let curMin' := min x (curMin + x)
        let bestMin' := min bestMin curMin'
        go (i + 1) total' curMax' bestMax' curMin' bestMin'
      else
        (total, bestMax, bestMin)
    termination_by nums.size - i

    let st := go 1 first first first first first
    let total : Int := st.1
    let bestMax : Int := st.2.1
    let bestMin : Int := st.2.2

    if bestMax < 0 then
      bestMax
    else
      max bestMax (total - bestMin)
end Impl

section TestCases
-- Test case 1: Example 1
-- Input: nums = [1,-2,3,-2]
-- Output: 3
-- Explanation: Subarray [3] has maximum sum 3.
def test1_nums : Array Int := #[1, -2, 3, -2]
def test1_Expected : Int := 3

-- Test case 2: Example 2 (wrap-around optimal)
def test2_nums : Array Int := #[5, -3, 5]
def test2_Expected : Int := 10

-- Test case 3: Example 3 (all negative)
def test3_nums : Array Int := #[-3, -2, -3]
def test3_Expected : Int := -2

-- Test case 4: Single element (must choose that element)
def test4_nums : Array Int := #[7]
def test4_Expected : Int := 7

-- Test case 5: All positive (best is whole array)
def test5_nums : Array Int := #[2, 3, 1]
def test5_Expected : Int := 6

-- Test case 6: Wrap-around beats any linear segment
-- Best is taking last and first element: 8 + 8 = 16
def test6_nums : Array Int := #[8, -1, -3, 8]
def test6_Expected : Int := 16

-- Test case 7: Contains zeros; best sum can be 0 even with negatives present
-- E.g., choose subarray [0]
def test7_nums : Array Int := #[0, -5, 0]
def test7_Expected : Int := 0

-- Test case 8: Two elements (smallest non-trivial size)
def test8_nums : Array Int := #[-1, 2]
def test8_Expected : Int := 2

-- Test case 9: Multiple candidates; maximum is achieved by a non-wrapping segment
-- Best is [3, -1, 2] with sum 4
def test9_nums : Array Int := #[3, -1, 2, -1]
def test9_Expected : Int := 4

-- Recommend to validate: all-negative arrays, wrap-around-optimal cases, single-element arrays
end TestCases

section ProofHelpers

-- ══════════════════════════════════════════════
-- Helper definitions for Kadane's algorithm
-- ══════════════════════════════════════════════

/-- Partial sum of first i elements: nums[0] + nums[1] + ... + nums[i-1] -/
def psum (nums : Array Int) (i : Nat) : Int :=
  (Finset.range i).sum (fun j => nums[j]!)

/-- Linear (non-wrapping) subarray sum: nums[s] + nums[s+1] + ... + nums[s+l-1] -/
def linSum (nums : Array Int) (s l : Nat) : Int :=
  (Finset.range l).sum (fun j => nums[s + j]!)

/-- Maximum subarray sum ending at position j (Kadane's curMax) -/
def kadMaxEnd (nums : Array Int) : Nat → Int
  | 0 => nums[0]!
  | j + 1 => max (nums[j + 1]!) (kadMaxEnd nums j + nums[j + 1]!)

/-- Best maximum subarray sum up to position j (Kadane's bestMax) -/
def kadBestMax (nums : Array Int) : Nat → Int
  | 0 => nums[0]!
  | j + 1 => max (kadBestMax nums j) (kadMaxEnd nums (j + 1))

/-- Minimum subarray sum ending at position j (Kadane's curMin) -/
def kadMinEnd (nums : Array Int) : Nat → Int
  | 0 => nums[0]!
  | j + 1 => min (nums[j + 1]!) (kadMinEnd nums j + nums[j + 1]!)

/-- Best minimum subarray sum up to position j (Kadane's bestMin) -/
def kadBestMin (nums : Array Int) : Nat → Int
  | 0 => nums[0]!
  | j + 1 => min (kadBestMin nums j) (kadMinEnd nums (j + 1))

/-
PROBLEM
══════════════════════════════════════════════
Lemma 1: Go loop invariant
══════════════════════════════════════════════

The go function, when called with arguments matching the Kadane invariant at position i,
    returns (totalSum, bestMax(n-1), bestMin(n-1)).

PROVIDED SOLUTION
Prove by strong induction on nums.size - i (which is the termination measure of go).

Base case: i = nums.size. Then go returns immediately (the if condition i < nums.size is false). The result is (psum nums i, kadBestMax nums (i-1), kadBestMin nums (i-1)) = (psum nums nums.size, kadBestMax nums (nums.size - 1), kadBestMin nums (nums.size - 1)). ✓

Inductive case: i < nums.size. Unfold go one step using implementation.go.eq_1. After one step, go calls itself with:
- i' = i + 1
- total' = psum nums i + nums[i]! = psum nums (i+1)  [since psum nums (i+1) = psum nums i + nums[i]!, by Finset.sum_range_succ]
- curMax' = max (nums[i]!) (kadMaxEnd nums (i-1) + nums[i]!) = kadMaxEnd nums i  [by definition of kadMaxEnd]
- bestMax' = max (kadBestMax nums (i-1)) (kadMaxEnd nums i) = kadBestMax nums i  [by definition of kadBestMax]
- curMin' = min (nums[i]!) (kadMinEnd nums (i-1) + nums[i]!) = kadMinEnd nums i  [by definition of kadMinEnd]
- bestMin' = min (kadBestMin nums (i-1)) (kadMinEnd nums i) = kadBestMin nums i  [by definition of kadBestMin]

So the recursive call is go (i+1) (psum nums (i+1)) (kadMaxEnd nums i) (kadBestMax nums i) (kadMinEnd nums i) (kadBestMin nums i), which by the IH (with i+1) equals the desired result.

Key: use `Nat.sub_add_cancel` or omega to handle the `i + 1 - 1 = i` simplification, and use `Finset.sum_range_succ` for the psum step.

Prove by induction on nums.size - i.

Base case: i = nums.size. Then the if condition i < nums.size is false, so go returns (psum nums i, kadBestMax nums (i-1), kadBestMin nums (i-1)). Since i = nums.size, this equals the target. Use implementation.go.eq_1 to unfold, then simp with the condition ¬(i < nums.size).

Inductive case: i < nums.size. Unfold go one step using implementation.go.eq_1. The function computes:
- x = nums[i]!
- total' = psum nums i + nums[i]!
- curMax' = max (nums[i]!) (kadMaxEnd nums (i-1) + nums[i]!)
- bestMax' = max (kadBestMax nums (i-1)) curMax'
- curMin' = min (nums[i]!) (kadMinEnd nums (i-1) + nums[i]!)
- bestMin' = min (kadBestMin nums (i-1)) curMin'

Then it calls go (i+1) total' curMax' bestMax' curMin' bestMin'.

Key observations:
1. total' = psum nums i + nums[i]! = psum nums (i+1)  by Finset.sum_range_succ
2. curMax' = max (nums[i]!) (kadMaxEnd nums (i-1) + nums[i]!)
   Since i ≥ 1, i-1+1 = i, so kadMaxEnd nums i = max (nums[i]!) (kadMaxEnd nums (i-1) + nums[i]!)
   Thus curMax' = kadMaxEnd nums i. But we need i-1 in the def to match: kadMaxEnd nums ((i+1)-1) = kadMaxEnd nums i.
3. bestMax' = max (kadBestMax nums (i-1)) (kadMaxEnd nums i) = kadBestMax nums i (since kadBestMax nums (i-1+1) = max (kadBestMax nums (i-1)) (kadMaxEnd nums i)). And (i+1)-1 = i.
4. Similarly for min.

So the recursive call matches go_invariant at i+1, and by IH we get the result.

To handle the Nat subtraction i-1, note that i ≥ 1 so i-1+1 = i. Use omega or Nat.sub_add_cancel for this.

Use `induction nums.size - i` or better, use `Nat.strongRecOn` or just unfold the definition and apply IH. Actually, since go has termination_by nums.size - i, you can use induction on a natural number k where k = nums.size - i, with generalization over i.

Here's the structure:
```
  induction h : nums.size - i with
  | zero => -- i = nums.size, base case
  | succ k ih => -- i < nums.size, inductive step
```
-/
lemma go_invariant (nums : Array Int) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ nums.size) :
    implementation.go nums i (psum nums i) (kadMaxEnd nums (i - 1))
      (kadBestMax nums (i - 1)) (kadMinEnd nums (i - 1)) (kadBestMin nums (i - 1)) =
    (psum nums nums.size, kadBestMax nums (nums.size - 1), kadBestMin nums (nums.size - 1)) := by
  -- By induction on $j = \text{nums.size} - i$, we can show that the go function's state at step $i$ is equivalent to the state at step $i+1$, and so on, until $i$ reaches $\text{nums.size}$.
  have h_ind : ∀ j, i + j ≤ nums.size → implementation.go nums i (psum nums i) (kadMaxEnd nums (i - 1)) (kadBestMax nums (i - 1)) (kadMinEnd nums (i - 1)) (kadBestMin nums (i - 1)) = implementation.go nums (i + j) (psum nums (i + j)) (kadMaxEnd nums (i + j - 1)) (kadBestMax nums (i + j - 1)) (kadMinEnd nums (i + j - 1)) (kadBestMin nums (i + j - 1)) := by
    intro j hj
    induction' j with j ih
    aesop;
    rw [ ih ( by linarith ), Nat.add_succ, implementation.go ];
    rw [ if_pos ( by linarith ) ] ; rcases k : i + j with ( _ | k ) <;> simp_all +decide [ Finset.sum_range_succ, psum ] ;
    congr;
  convert h_ind ( nums.size - i ) ( by omega ) using 1 ; simp +decide [ Nat.add_sub_of_le hi2 ];
  unfold implementation.go; aesop;

/-
PROBLEM
══════════════════════════════════════════════
Lemma 2: Go produces the correct result
══════════════════════════════════════════════

Starting from initial values nums[0]!, the go function returns
    (totalSum, maxKadane, minKadane).

PROVIDED SOLUTION
The initial values at i=1 match the Kadane invariant: psum nums 1 = Finset.sum (range 1) = nums[0]!, kadMaxEnd nums 0 = nums[0]!, kadBestMax nums 0 = nums[0]!, kadMinEnd nums 0 = nums[0]!, kadBestMin nums 0 = nums[0]!. So we can rewrite the LHS to match go_invariant's form at i=1 and apply go_invariant. Use simp with psum, kadMaxEnd, kadBestMax, kadMinEnd, kadBestMin to simplify the initial values, then apply go_invariant.
-/
lemma go_result (nums : Array Int) (hn : 0 < nums.size) :
    implementation.go nums 1 (nums[0]!) (nums[0]!) (nums[0]!) (nums[0]!) (nums[0]!) =
    (psum nums nums.size, kadBestMax nums (nums.size - 1), kadBestMin nums (nums.size - 1)) := by
  convert go_invariant nums 1 ( by linarith ) ( by linarith ) using 1;
  unfold psum kadMaxEnd kadBestMax kadMinEnd kadBestMin; aesop;

/-
PROBLEM
══════════════════════════════════════════════
Lemma 3: Kadane max is an upper bound on linear subarray sums
══════════════════════════════════════════════

kadBestMax(n-1) ≥ sum of any valid linear (non-wrapping) subarray.

PROVIDED SOLUTION
Prove by induction. First show by induction on j that kadMaxEnd nums j ≥ linSum nums s l for any s, l with s + l = j + 1, l ≥ 1 (i.e., subarrays ending at position j).

Sub-lemma: kadMaxEnd nums j = max over l ∈ [1, j+1] of linSum nums (j+1-l) l. Prove by induction on j:
- j=0: kadMaxEnd nums 0 = nums[0]! = linSum nums 0 1. The max over l ∈ [1,1] is just linSum nums 0 1. ✓
- j→j+1: kadMaxEnd nums (j+1) = max(nums[j+1]!, kadMaxEnd nums j + nums[j+1]!)
  By IH, kadMaxEnd nums j = max over l ∈ [1, j+1] of linSum nums (j+1-l) l
  kadMaxEnd nums j + nums[j+1]! = max over l of (linSum nums (j+1-l) l + nums[j+1]!)
  = max over l of linSum nums (j+1-l) (l+1)  [extending by one element]
  = max over l' ∈ [2, j+2] of linSum nums (j+2-l') l'
  And nums[j+1]! = linSum nums (j+1) 1 = linSum nums (j+2-1) 1
  So max(nums[j+1]!, kadMaxEnd nums j + nums[j+1]!) = max over l' ∈ [1, j+2] of linSum nums (j+2-l') l' ✓

So kadMaxEnd nums j ≥ linSum nums s l when s + l = j + 1, l ≥ 1.

Then kadBestMax nums j = max over j' ∈ [0, j] of kadMaxEnd nums j' ≥ kadMaxEnd nums (s+l-1) ≥ linSum nums s l.
And kadBestMax is non-decreasing, so kadBestMax nums (n-1) ≥ kadBestMax nums (s+l-1) ≥ linSum nums s l.

Actually, let me state it more directly. We want to show: for any s, l with s + l ≤ n and l ≥ 1, linSum nums s l ≤ kadBestMax nums (n-1).

Proof: linSum nums s l ≤ kadMaxEnd nums (s+l-1) ≤ kadBestMax nums (s+l-1) ≤ kadBestMax nums (n-1).

Step 1: linSum nums s l ≤ kadMaxEnd nums (s+l-1). By the sub-lemma, kadMaxEnd nums (s+l-1) is the max of linSum nums (s+l-l') l' for l' ∈ [1, s+l]. Taking l' = l gives linSum nums s l.

Step 2: kadMaxEnd nums j ≤ kadBestMax nums j. By definition, kadBestMax nums j = max(kadBestMax nums (j-1), kadMaxEnd nums j) ≥ kadMaxEnd nums j.

Step 3: kadBestMax is non-decreasing. kadBestMax nums (j+1) = max(kadBestMax nums j, kadMaxEnd nums (j+1)) ≥ kadBestMax nums j.

This might be too complex for a single subagent call. Let me just try it.
-/
lemma kadBestMax_upper (nums : Array Int) (hn : 0 < nums.size) (s l : Nat)
    (hsl : s + l ≤ nums.size) (hl : 1 ≤ l) :
    linSum nums s l ≤ kadBestMax nums (nums.size - 1) := by
  have h_kadMaxEnd : ∀ (j : ℕ), j < nums.size → ∀ (s l : ℕ), s + l = j + 1 → 1 ≤ l → linSum nums s l ≤ kadMaxEnd nums j := by
    intros j hj s l hsl hl
    induction' j with j ih generalizing s l
    all_goals generalize_proofs at *;
    · rcases s with ( _ | _ | s ) <;> rcases l with ( _ | _ | l ) <;> simp_all +arith +decide only [linSum] ; aesop;
    · rcases l with ( _ | l ) <;> simp_all +decide [ linSum, kadMaxEnd ];
      specialize ih ( by linarith ) ( s ) ( l ) ; simp_all +decide [ Finset.sum_range_succ ];
      by_cases hl : 1 ≤ l <;> simp_all +decide [ show s + l = j + 1 by linarith ];
  refine' le_trans ( h_kadMaxEnd ( s + l - 1 ) _ s l _ _ ) _;
  · omega;
  · rw [ Nat.sub_add_cancel ( by linarith ) ];
  · grind;
  · refine' le_trans _ ( show kadBestMax nums ( s + l - 1 ) ≤ kadBestMax nums ( nums.size - 1 ) from _ );
    · induction' s + l - 1 with j ih;
      · rfl;
      · exact le_max_right _ _;
    · -- By definition of `kadBestMax`, we know that `kadBestMax nums j` is non-decreasing.
      have h_kadBestMax_mono : ∀ (j k : ℕ), j ≤ k → j < nums.size → k < nums.size → kadBestMax nums j ≤ kadBestMax nums k := by
        intros j k hjk hj hk
        induction' hjk with j hjk ih;
        · rfl;
        · exact le_trans ( ih ( Nat.lt_of_succ_lt hk ) ) ( by exact le_max_left _ _ );
      exact h_kadBestMax_mono _ _ ( Nat.sub_le_sub_right hsl 1 ) ( Nat.lt_of_lt_of_le ( Nat.sub_lt ( by linarith ) zero_lt_one ) ( by linarith ) ) ( Nat.sub_lt hn zero_lt_one )

/-
PROBLEM
══════════════════════════════════════════════
Lemma 4: Kadane max is achieved by some linear subarray
══════════════════════════════════════════════

There exists a valid linear subarray whose sum equals kadBestMax(n-1).

PROVIDED SOLUTION
Prove by induction on nums.size - 1.

Base case (n=1): kadBestMax nums 0 = nums[0]! = linSum nums 0 1. Take s=0, l=1. ✓

Inductive case: kadBestMax nums (j+1) = max(kadBestMax nums j, kadMaxEnd nums (j+1)).
Either kadBestMax nums (j+1) = kadBestMax nums j (use IH to get witness) or kadBestMax nums (j+1) = kadMaxEnd nums (j+1).

For the second case, we need kadMaxEnd nums (j+1) is achieved by some subarray ending at j+1. By induction on j, kadMaxEnd nums j is either nums[j+1]! (take s=j+1, l=1) or kadMaxEnd nums j + nums[j+1]! (extend the witness for kadMaxEnd nums j by one element). So kadMaxEnd is always achieved.

Then for kadBestMax, either it equals kadBestMax of a smaller index (use IH) or it equals kadMaxEnd (which is achieved as shown).

The key is to prove a helper: kadMaxEnd nums j is achieved, i.e., ∃ s, s + l = j + 1 ∧ 1 ≤ l ∧ linSum nums s l = kadMaxEnd nums j. Prove by induction on j.
-/
lemma kadBestMax_achieved (nums : Array Int) (hn : 0 < nums.size) :
    ∃ s l, s + l ≤ nums.size ∧ 1 ≤ l ∧
    linSum nums s l = kadBestMax nums (nums.size - 1) := by
  -- By definition of `kadBestMax`, there exists some `j` such that `kadBestMax nums j = kadBestMax nums (nums.size - 1)`.
  obtain ⟨j, hj⟩ : ∃ j, j < nums.size ∧ kadMaxEnd nums j = kadBestMax nums (nums.size - 1) := by
    have h_exists_j : ∀ j, j < nums.size → ∃ k, k < nums.size ∧ kadMaxEnd nums k = kadBestMax nums j := by
      intro j hj
      induction' j with j ih;
      · exact ⟨ 0, hj, rfl ⟩;
      · rw [ show kadBestMax nums ( j + 1 ) = max ( kadBestMax nums j ) ( kadMaxEnd nums ( j + 1 ) ) by rfl ];
        grind;
    exact h_exists_j _ ( Nat.pred_lt hn.ne' );
  -- By definition of `kadMaxEnd`, there exists some `l` such that `linSum nums (j - l + 1) l = kadMaxEnd nums j`.
  obtain ⟨l, hl⟩ : ∃ l, 1 ≤ l ∧ l ≤ j + 1 ∧ linSum nums (j + 1 - l) l = kadMaxEnd nums j := by
    have h_kadMaxEnd : ∀ j, ∃ l, 1 ≤ l ∧ l ≤ j + 1 ∧ linSum nums (j + 1 - l) l = kadMaxEnd nums j := by
      intro j
      induction' j with j ih;
      · use 1
        simp [linSum, kadMaxEnd];
      · -- By definition of `kadMaxEnd`, we know that `kadMaxEnd nums (j + 1)` is either `nums[j + 1]!` or `kadMaxEnd nums j + nums[j + 1]!`.
        have h_kadMaxEnd_succ : kadMaxEnd nums (j + 1) = max (nums[j + 1]!) (kadMaxEnd nums j + nums[j + 1]!) := by
          rfl;
        cases max_cases ( nums[j + 1]! ) ( kadMaxEnd nums j + nums[j + 1]! ) <;> simp_all +decide [ linSum ];
        · exact ⟨ 1, by norm_num, by linarith, by norm_num ⟩;
        · obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := ih; use l + 1; simp_all +decide [ Finset.sum_range_succ ] ;
    exact h_kadMaxEnd j;
  exact ⟨ j + 1 - l, l, by omega, hl.1, by linarith ⟩

/-
PROBLEM
══════════════════════════════════════════════
Lemma 5: Kadane min is a lower bound on linear subarray sums
══════════════════════════════════════════════

kadBestMin(n-1) ≤ sum of any valid linear (non-wrapping) subarray.

PROVIDED SOLUTION
Symmetric to kadBestMax_upper. Prove by showing kadMinEnd nums j ≤ linSum nums s l for any subarray ending at j, then kadBestMin nums j ≤ kadMinEnd nums j' for the appropriate j', and kadBestMin is non-increasing.

Step 1: kadMinEnd nums j is the min of linSum nums (j+1-l) l for l ∈ [1, j+1] (by induction on j, similar to kadMaxEnd).
Step 2: kadMinEnd nums j ≤ kadBestMin nums j (by definition).
Step 3: kadBestMin is non-increasing (kadBestMin nums (j+1) = min(kadBestMin nums j, ...) ≤ kadBestMin nums j).
Step 4: Combine: kadBestMin nums (n-1) ≤ kadBestMin nums (s+l-1) ≤ kadMinEnd nums (s+l-1) ≤ linSum nums s l.
-/
lemma kadBestMin_lower (nums : Array Int) (hn : 0 < nums.size) (s l : Nat)
    (hsl : s + l ≤ nums.size) (hl : 1 ≤ l) :
    kadBestMin nums (nums.size - 1) ≤ linSum nums s l := by
  -- By definition of `kadMinEnd`, we know that `kadMinEnd nums j ≤ linSum nums s l` for any `s` and `l` such that `s + l = j + 1`.
  have h_kadMinEnd_le : ∀ j s l, s + l = j + 1 → 1 ≤ l → s < nums.size → l ≤ nums.size → kadMinEnd nums j ≤ linSum nums s l := by
    intros j s l hj hl hs hl'
    induction' l with l ih generalizing s j;
    · contradiction;
    · rcases l with ( _ | l ) <;> simp_all +decide [ Finset.sum_range_succ ];
      · -- By definition of `kadMinEnd`, we know that `kadMinEnd nums j` is the minimum of `nums[j]!` and `kadMinEnd nums (j-1) + nums[j]!`.
        have h_kadMinEnd_def : ∀ j, kadMinEnd nums j ≤ nums[j]! := by
          intro j; induction' j with j ih <;> simp +decide [ *, kadMinEnd ] ;
        convert h_kadMinEnd_def j using 1;
        unfold linSum; aesop;
      · have h_kadMinEnd_le : kadMinEnd nums j = min (nums[j]!) (kadMinEnd nums (j - 1) + nums[j]!) := by
          rcases j <;> simp_all +decide [ kadMinEnd ];
          grind;
        have h_kadMinEnd_le : linSum nums s (l + 2) = linSum nums s (l + 1) + nums[(s + (l + 1))]! := by
          unfold linSum; simp +decide [ Finset.sum_range_succ ] ;
        grind +ring;
  -- By definition of `kadBestMin`, we know that `kadBestMin nums j ≤ kadMinEnd nums j'` for any `j' ≤ j`.
  have h_kadBestMin_le : ∀ j j', j' ≤ j → kadBestMin nums j ≤ kadMinEnd nums j' := by
    intros j j' hj'j
    induction' j with j ih generalizing j';
    · aesop;
    · cases hj'j <;> simp_all +decide [ kadBestMin ];
  exact le_trans ( h_kadBestMin_le _ _ ( show s + l - 1 ≤ nums.size - 1 from Nat.sub_le_sub_right hsl _ ) ) ( h_kadMinEnd_le _ _ _ ( by omega ) hl ( by omega ) ( by omega ) )

/-
PROBLEM
══════════════════════════════════════════════
Lemma 6: Kadane min is achieved by some linear subarray
══════════════════════════════════════════════

There exists a valid linear subarray whose sum equals kadBestMin(n-1).

PROVIDED SOLUTION
Symmetric to kadBestMax_achieved. kadBestMin nums (j+1) = min(kadBestMin nums j, kadMinEnd nums (j+1)). Either equals kadBestMin nums j (use IH) or kadMinEnd nums (j+1). kadMinEnd is achieved by some subarray ending at j+1 (by induction: either the single element or extending the previous kadMinEnd witness).

Symmetric to kadBestMax_achieved. The proof has two parts:

Part 1: Show that kadBestMin nums j is achieved by kadMinEnd nums j' for some j' ≤ j.
By induction on j:
- Base: kadBestMin nums 0 = nums[0]! = kadMinEnd nums 0. Take j'=0.
- Step: kadBestMin nums (j+1) = min(kadBestMin nums j, kadMinEnd nums (j+1)).
  If min = kadBestMin nums j, use IH to get j' ≤ j ≤ j+1.
  If min = kadMinEnd nums (j+1), take j' = j+1.
  Use `min_cases` to do the case split.

Part 2: Show that kadMinEnd nums j' is achieved by some linSum.
By induction on j':
- Base: kadMinEnd nums 0 = nums[0]! = linSum nums 0 1. Take s=0, l=1.
- Step: kadMinEnd nums (j'+1) = min(nums[j'+1]!, kadMinEnd nums j' + nums[j'+1]!).
  If min = nums[j'+1]!, take s=j'+1, l=1. linSum nums (j'+1) 1 = nums[j'+1]!.
  If min = kadMinEnd nums j' + nums[j'+1]!, by IH we have s, l with linSum = kadMinEnd j'.
  Then linSum nums s (l+1) = linSum nums s l + nums[s+l]! = kadMinEnd j' + nums[j'+1]!.
  (Here s+l = j'+1, so nums[s+l]! = nums[j'+1]!.)
  Use `min_cases` for the case split.

Combine: get j' from Part 1, then s, l from Part 2. The witness is (s, l).
Verify s + l ≤ nums.size: s + l = j' + 1 ≤ j + 1 ≤ nums.size.
-/
lemma kadBestMin_achieved (nums : Array Int) (hn : 0 < nums.size) :
    ∃ s l, s + l ≤ nums.size ∧ 1 ≤ l ∧
    linSum nums s l = kadBestMin nums (nums.size - 1) := by
  -- We'll use induction on `j` to show that `kadBestMin nums j` is achieved by some linear subarray.
  have h_ind : ∀ j, j < nums.size → ∃ s l, s + l ≤ nums.size ∧ 1 ≤ l ∧ linSum nums s l = kadBestMin nums j := by
    intro j hj
    obtain ⟨j', hj'⟩ : ∃ j', j' ≤ j ∧ kadBestMin nums j = kadMinEnd nums j' := by
      induction' j with j ih;
      · exact ⟨ 0, le_rfl, rfl ⟩;
      · cases min_cases ( kadBestMin nums j ) ( kadMinEnd nums ( j + 1 ) ) <;> simp +decide [ *, kadBestMin ];
        · exact Exists.elim ( ih ( Nat.lt_of_succ_lt hj ) ) fun j' hj' => ⟨ j', Nat.le_succ_of_le hj'.1, hj'.2 ⟩;
        · exact ⟨ j + 1, le_rfl, rfl ⟩;
    -- By induction on `j'`, we can show that `kadMinEnd nums j'` is achieved by some linear subarray.
    have h_ind_j' : ∀ j', j' < nums.size → ∃ s l, s + l = j' + 1 ∧ 1 ≤ l ∧ linSum nums s l = kadMinEnd nums j' := by
      intro j' hj'
      induction' j' with j' ih;
      · use 0, 1
        simp [linSum, kadMinEnd];
      · -- By definition of `kadMinEnd`, we have `kadMinEnd nums (j' + 1) = min (nums[j' + 1]!) (kadMinEnd nums j' + nums[j' + 1]!)`.
        have h_kadMinEnd_succ : kadMinEnd nums (j' + 1) = min (nums[j' + 1]!) (kadMinEnd nums j' + nums[j' + 1]!) := by
          rfl;
        cases min_cases ( nums[j' + 1]! ) ( kadMinEnd nums j' + nums[j' + 1]! ) <;> simp_all +decide [ linSum ];
        · use j' + 1, 1
          simp [Finset.sum_range_succ];
          grind;
        · obtain ⟨ s, l, hs, hl, h ⟩ := ih ( Nat.lt_of_succ_lt hj' ) ; use s, l + 1; simp_all +decide [ Finset.sum_range_succ ] ;
          linarith;
    exact Exists.elim ( h_ind_j' j' ( by linarith ) ) fun s hs => Exists.elim hs fun l hl => ⟨ s, l, by linarith, hl.2.1, by aesop ⟩;
  exact h_ind _ ( Nat.pred_lt hn.ne' )

/-
  -- By definition of `kadMinEnd`, there exists some `l` such that `linSum nums (j' + 1 - l) l = kadMinEnd nums j'`.
  obtain ⟨l, hl⟩ : ∃ l, 1 ≤ l ∧ l ≤ j' + 1 ∧ linSum nums (j' + 1 - l) l = kadMinEnd nums j' := by
    have h_ind : ∀ j, ∃ l, 1 ≤ l ∧ l ≤ j + 1 ∧ linSum nums (j + 1 - l) l = kadMinEnd nums j := by
      intro j
      induction' j with j ih;
      · use 1
        simp [linSum, kadMinEnd];
      · -- By definition of `kadMinEnd`, we have `kadMinEnd nums (j + 1) = min (nums[j + 1]!) (kadMinEnd nums j + nums[j + 1]!)`.
        have h_kadMinEnd_succ : kadMinEnd nums (j + 1) = min (nums[j + 1]!) (kadMinEnd nums j + nums[j + 1]!) := by
          rfl;
        cases min_cases ( nums[j + 1]! ) ( kadMinEnd nums j + nums[j + 1]! ) <;> simp_all +decide [ linSum ];
        · exact ⟨ 1, by norm_num, by linarith, by norm_num ⟩;
        · obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := ih; use l + 1; simp_all +decide [ Finset.sum_range_succ ] ;
    exact h_ind j';
  exact ⟨ j' + 1 - l, l, by omega, hl.1, by linarith ⟩
-/

/-
PROBLEM
══════════════════════════════════════════════
Lemma 7: circSegmentSum for non-wrapping segments
══════════════════════════════════════════════

For non-wrapping segments (start + len ≤ n), circSegmentSum = linSum.

PROVIDED SOLUTION
Unfold circSegmentSum and linSum. Both are sums over Finset.range len. For each i in [0, len), since start + i < start + len ≤ nums.size, we have (start + i) % nums.size = start + i (using Nat.mod_eq_of_lt). So each summand is equal. Use Finset.sum_congr.
-/
lemma circSeg_nonwrap (nums : Array Int) (start len : Nat)
    (hn : 0 < nums.size) (hsl : start + len ≤ nums.size) :
    circSegmentSum nums start len = linSum nums start len := by
  exact Finset.sum_congr rfl fun i hi => by rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp hi ] ) ] ;

/-
PROBLEM
══════════════════════════════════════════════
Lemma 8: circSegmentSum for wrapping segments
══════════════════════════════════════════════

For wrapping segments (start + len > n, start < n, len ≤ n),
    circSegmentSum = totalSum - linSum of the "gap".

PROVIDED SOLUTION
Split the circular sum into two parts: indices where (start+i) mod n >= start (the "tail" part), and indices where (start+i) mod n < start (the "head" part that wraps around).

More precisely: circSegmentSum nums start len = sum_{i=0}^{len-1} nums[(start+i) % n]!

Split the range [0, len) at position (n - start): for i < n - start, (start + i) % n = start + i. For i >= n - start, (start + i) % n = start + i - n.

So circSegmentSum = sum_{i=0}^{n-start-1} nums[start+i]! + sum_{i=n-start}^{len-1} nums[start+i-n]!
= linSum nums start (n-start) + sum_{j=0}^{len-(n-start)-1} nums[j]!  (substituting j = i - (n-start), so j goes from 0 to start+len-n-1)
= linSum nums start (n-start) + linSum nums 0 (start+len-n)

And psum nums n = linSum nums 0 n = linSum nums 0 (start+len-n) + linSum nums (start+len-n) (n-len) + linSum nums start (n-start)
Wait, we need: linSum nums 0 n = linSum nums 0 (start+len-n) + linSum nums (start+len-n) (start - (start+len-n)) + linSum nums start (n-start).
Where start - (start+len-n) = n - len.
Let g = start+len-n, gl = n-len. Then g + gl = start.
So: linSum 0 n = linSum 0 g + linSum g gl + linSum start (n-start).
And circSeg = linSum start (n-start) + linSum 0 g.
Therefore circSeg = psum n - linSum g gl = psum n - linSum (start+len-n) (n-len).

The key Finset identity is: Finset.sum_range_add: sum over [0, a+b) = sum over [0, a) + sum over [a, a+b). Use Finset.sum_range_add_sum_Ico or similar to split the sum.

For the mod arithmetic, use Nat.add_mod_right, Nat.mod_eq_of_lt, etc.
-/
lemma circSeg_wrap (nums : Array Int) (start len : Nat)
    (hn : 0 < nums.size) (hs : start < nums.size) (hl1 : 1 ≤ len) (hln : len ≤ nums.size)
    (hwrap : nums.size < start + len) :
    circSegmentSum nums start len =
    psum nums nums.size - linSum nums (start + len - nums.size) (nums.size - len) := by
  -- Split the sum into two parts: from `start` to `nums.size - 1` and from `0` to `start + len - nums.size - 1`.
  have h_split : circSegmentSum nums start len = (Finset.range (nums.size - start)).sum (fun i => nums[(start + i) % nums.size]!) + (Finset.range (start + len - nums.size)).sum (fun i => nums[(i) % nums.size]!) := by
    unfold circSegmentSum;
    rw [ ← Finset.sum_range_add_sum_Ico _ ( show nums.size - start ≤ len from by omega ) ];
    simp +arith +decide [ Finset.sum_Ico_eq_sum_range, Nat.sub_add_comm hln ];
    rw [ show len - ( nums.size - start ) = start + len - nums.size from by omega ] ; refine' Finset.sum_congr rfl fun i hi => _ ; simp +decide [ add_assoc, Nat.mod_eq_of_lt, hs, hl1, hln, hwrap ] ;
    rw [ show start + ( i + ( nums.size - start ) ) = i + nums.size by linarith [ Nat.sub_add_cancel hs.le ] ] ; simp +decide [ Nat.mod_eq_of_lt, hs, hl1, hln, hwrap ];
  -- The first part of the split sum is the sum of the elements from `start` to `nums.size - 1`.
  have h_first_part : (Finset.range (nums.size - start)).sum (fun i => nums[(start + i) % nums.size]!) = (psum nums nums.size) - (psum nums start) := by
    have h_first_part : (Finset.range (nums.size - start)).sum (fun i => nums[(start + i) % nums.size]!) = (Finset.range (nums.size)).sum (fun i => nums[i]!) - (Finset.range start).sum (fun i => nums[i]!) := by
      rw [ ← Finset.sum_Ico_eq_sub _ ];
      · rw [ Finset.sum_Ico_eq_sum_range ];
        exact Finset.sum_congr rfl fun i hi => by rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hs.le ] ) ] ;
      · linarith;
    exact h_first_part;
  -- The second part of the split sum is the sum of the elements from `0` to `start + len - nums.size - 1`.
  have h_second_part : (Finset.range (start + len - nums.size)).sum (fun i => nums[(i) % nums.size]!) = (psum nums (start + len - nums.size)) := by
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( by linarith : nums.size ≤ start + len ) ] ) ];
  -- By definition of `linSum`, we can expand it as the sum of the elements from `start + len - nums.size` to `nums.size - 1`.
  have h_lin_sum : linSum nums (start + len - nums.size) (nums.size - len) = (psum nums (start + len - nums.size + (nums.size - len))) - (psum nums (start + len - nums.size)) := by
    unfold linSum psum; simp +decide [ Finset.sum_range_add ] ;
  rw [ show start + len - nums.size + ( nums.size - len ) = start by omega ] at h_lin_sum ; linarith

/-
PROBLEM
══════════════════════════════════════════════
Lemma 9: psum n = linSum 0 n
══════════════════════════════════════════════

PROVIDED SOLUTION
Unfold psum and linSum. Both are sums over Finset.range nums.size of nums[j]! (linSum has s=0 so s+j = 0+j = j). Use simp or congr.
-/
lemma psum_eq_linSum_zero (nums : Array Int) :
    psum nums nums.size = linSum nums 0 nums.size := by
  unfold psum linSum; aesop;

/-
PROBLEM
══════════════════════════════════════════════
Lemma 10: When bestMax < 0, every element is negative
══════════════════════════════════════════════

If kadBestMax < 0, then every element of the array is negative.

PROVIDED SOLUTION
Each element nums[j]! is a single-element linear subarray (s=j, l=1), so kadBestMax ≥ nums[j]! (by elem_le_kadBestMax). If kadBestMax < 0, then nums[j]! ≤ kadBestMax < 0, so nums[j]! < 0.
-/
lemma all_neg_of_kadBestMax_neg (nums : Array Int) (hn : 0 < nums.size)
    (hbm : kadBestMax nums (nums.size - 1) < 0) (j : Nat) (hj : j < nums.size) :
    nums[j]! < 0 := by
  -- Since `kadBestMax` is an upper bound for linear subarray sums, and `kadBestMax < 0`, every linear subarray sum must be negative.
  have h_linear_neg : ∀ s l, s + l ≤ nums.size → 1 ≤ l → linSum nums s l < 0 := by
    exact fun s l hsl hl => lt_of_le_of_lt ( kadBestMax_upper nums hn s l hsl hl ) hbm;
  convert h_linear_neg j 1 ( by linarith ) ( by linarith ) using 1;
  unfold linSum; aesop;

/-
PROBLEM
══════════════════════════════════════════════
Lemma 11: Each element ≤ kadBestMax
══════════════════════════════════════════════

PROVIDED SOLUTION
The single-element subarray [nums[j]] is a valid linear subarray (s=j, l=1). Its sum = nums[j]!. By kadBestMax_upper, nums[j]! ≤ kadBestMax. But kadBestMax_upper has a sorry. Instead, prove directly by induction on nums.size - 1. kadBestMax nums j = max (kadBestMax nums (j-1)) (kadMaxEnd nums j). And kadMaxEnd nums j ≥ nums[j]! (since nums[j]! is one option in the max). Then kadBestMax nums j ≥ nums[j]!. For j < target, kadBestMax is non-decreasing: kadBestMax nums (j+1) = max (kadBestMax nums j) ... ≥ kadBestMax nums j. So kadBestMax nums (n-1) ≥ kadBestMax nums j ≥ nums[j]!.
-/
lemma elem_le_kadBestMax (nums : Array Int) (hn : 0 < nums.size)
    (j : Nat) (hj : j < nums.size) :
    nums[j]! ≤ kadBestMax nums (nums.size - 1) := by
  -- By definition ofBEST, BEST is the maximum possible sum of any linear subarray.
  have BEST_ge_single : ∀ j, j < nums.size → nums[j]! ≤ kadBestMax nums (nums.size - 1) := by
    intro j hj
    have h_single : linSum nums j 1 ≤ kadBestMax nums (nums.size - 1) := by
      convert kadBestMax_upper nums hn j 1 ( by linarith ) ( by linarith ) using 1;
    unfold linSum at h_single; aesop;
  exact BEST_ge_single j hj

/-
PROBLEM
══════════════════════════════════════════════
Lemma 12: Wrapping sum ≤ bestMax when all elements negative
══════════════════════════════════════════════

When all elements are negative and the circular subarray wraps (len ≥ 2),
    its sum ≤ kadBestMax.

PROVIDED SOLUTION
When all elements are negative: wrapping means start + len > nums.size, so len ≥ 2 (since start < nums.size, len > nums.size - start ≥ 1, i.e., len ≥ 2). The circular subarray sum = sum of len elements of the array, each ≤ kadBestMax (by elem_le_kadBestMax). Since all elements are negative (by hallneg), each element < 0, hence each element ≤ kadBestMax nums (nums.size - 1) < 0. The sum of len ≥ 2 such elements ≤ len * kadBestMax ≤ 2 * kadBestMax < kadBestMax (since kadBestMax < 0).

More precisely: circSegmentSum = sum of len terms, each of which is nums[(start+i) % nums.size]!. Since (start+i) % nums.size < nums.size, by hallneg each term < 0, hence each term ≤ kadBestMax (by elem_le_kadBestMax).

Actually, even more direct: use circSeg_wrap to write circSegmentSum = psum - linSum(gap). Then since gap is a valid linear subarray, linSum(gap) ≥ kadBestMin ≥ ... but this uses kadBestMin.

Alternative: circSegmentSum is the sum of len elements. len ≥ 2. Each element is some nums[k]! where k < nums.size, so each is < 0 by hallneg, and ≤ kadBestMax by elem_le_kadBestMax. For the first element, nums[(start) % nums.size]! ≤ kadBestMax. The remaining len-1 elements sum to something < 0 (since each is negative). So circSegmentSum < kadBestMax ≤ kadBestMax. Wait, that gives circSegmentSum < kadBestMax + 0 = kadBestMax. But I need ≤, so < suffices.

Concretely: let a = nums[(start) % nums.size]! and rest = sum of remaining len-1 terms. a ≤ kadBestMax. rest < 0 (sum of len-1 ≥ 1 negative terms). So circSegmentSum = a + rest < kadBestMax + 0 = kadBestMax. Hence ≤ follows from <.
-/
lemma wrap_le_kadBestMax_neg (nums : Array Int) (start len : Nat)
    (hn : 0 < nums.size) (hs : start < nums.size) (hl1 : 1 ≤ len) (hln : len ≤ nums.size)
    (hwrap : nums.size < start + len)
    (hallneg : ∀ j, j < nums.size → nums[j]! < 0) :
    circSegmentSum nums start len ≤ kadBestMax nums (nums.size - 1) := by
  rw [ circSegmentSum ];
  refine' le_trans _ ( elem_le_kadBestMax nums hn _ _ );
  rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr hl1 ) ];
  refine' add_le_of_nonpos_right _;
  · exact Finset.sum_nonpos fun x hx => le_of_lt ( hallneg _ <| Nat.mod_lt _ hn );
  · exact Nat.mod_lt _ hn

/-
PROBLEM
══════════════════════════════════════════════
Lemma 13: kadBestMax ≥ totalSum (the whole array is a valid linear subarray)
══════════════════════════════════════════════

PROVIDED SOLUTION
The whole array is a valid linear subarray (s=0, l=n). Its sum = linSum nums 0 n = psum nums n (by psum_eq_linSum_zero). By kadBestMax_upper, linSum nums 0 n ≤ kadBestMax. Hence psum nums n ≤ kadBestMax. But kadBestMax_upper has a sorry. Instead, prove directly. We can use kadBestMax_upper once it's proved, or prove it from the Kadane definitions by induction.
-/
lemma kadBestMax_ge_psum (nums : Array Int) (hn : 0 < nums.size) :
    psum nums nums.size ≤ kadBestMax nums (nums.size - 1) := by
  by_contra h_contra;
  obtain ⟨start, len, hsl, hl⟩ : ∃ start len : Nat, start + len ≤ nums.size ∧ 1 ≤ len ∧ linSum nums start len = psum nums nums.size := by
    unfold linSum psum; aesop;
  exact h_contra <| hl.2 ▸ kadBestMax_upper nums hn start len hsl hl.1

/-
PROBLEM
══════════════════════════════════════════════
Lemma 14: When total - bestMin > bestMax ≥ 0, the min subarray has length < n
══════════════════════════════════════════════

When bestMax ≥ 0 and total - bestMin > bestMax,
    there exists a min-achieving linear subarray with length < n.

PROVIDED SOLUTION
By kadBestMin_achieved, there exist s, l with s + l ≤ nums.size, 1 ≤ l, and linSum nums s l = kadBestMin nums (nums.size - 1). We claim l < nums.size.

Suppose l = nums.size for contradiction. Then s = 0 (since s + l ≤ nums.size and l = nums.size means s = 0). So linSum nums 0 nums.size = kadBestMin. But linSum nums 0 nums.size = psum nums nums.size (by psum_eq_linSum_zero). So kadBestMin = psum.

From hgt: kadBestMax < psum - kadBestMin = psum - psum = 0. So kadBestMax < 0. But hbm_nn says 0 ≤ kadBestMax. Contradiction!

So l < nums.size. Use the s, l from kadBestMin_achieved with the additional fact l < nums.size.
-/
lemma bestMin_short_witness (nums : Array Int) (hn : 0 < nums.size)
    (hbm_nn : 0 ≤ kadBestMax nums (nums.size - 1))
    (hgt : kadBestMax nums (nums.size - 1) < psum nums nums.size - kadBestMin nums (nums.size - 1)) :
    ∃ s l, s + l ≤ nums.size ∧ 1 ≤ l ∧ l < nums.size ∧
    linSum nums s l = kadBestMin nums (nums.size - 1) := by
  obtain ⟨ s, l, hsl, hl, h ⟩ := kadBestMin_achieved nums hn;
  by_cases hl_eq : l = nums.size;
  · simp_all +decide [ linSum ];
    exact absurd hgt ( by linarith! [ psum_eq_linSum_zero nums, kadBestMax_ge_psum nums hn ] );
  · exact ⟨ s, l, hsl, hl, lt_of_le_of_ne ( by linarith ) hl_eq, h ⟩

end ProofHelpers

section Proof

/-
PROBLEM
The implementation output equals the Kadane-based formula.

PROVIDED SOLUTION
Unfold postcondition and implementation. Split into achievability and maximality.

The precondition gives nums.size > 0, so the implementation doesn't return 0 (the if nums.size = 0 branch is not taken).

Use go_result to characterize the go output: st = (psum nums n, kadBestMax(n-1), kadBestMin(n-1)). So total = psum nums n, bestMax = kadBestMax(n-1), bestMin = kadBestMin(n-1).

**Case 1: bestMax < 0 (all negative)**
Result = bestMax = kadBestMax(n-1).

Achievability: By kadBestMax_achieved, ∃ s l with s+l ≤ n, 1 ≤ l, linSum s l = kadBestMax. This is a non-wrapping valid circular segment (start = s, len = l; isValidCircSegment holds since s < n [because s + l ≤ n and l ≥ 1, so s ≤ n-1]). circSegmentSum = linSum (by circSeg_nonwrap). So circSegmentSum = kadBestMax = result.

Maximality: For any valid (start, len):
- If start + len ≤ n (non-wrapping): circSegmentSum = linSum ≤ kadBestMax = result (by kadBestMax_upper and circSeg_nonwrap).
- If start + len > n (wrapping): circSegmentSum ≤ kadBestMax = result (by wrap_le_kadBestMax_neg, since bestMax < 0 implies all elements negative by all_neg_of_kadBestMax_neg).

**Case 2: bestMax ≥ 0**
Result = max(bestMax, total - bestMin) = max(kadBestMax, psum - kadBestMin).

Achievability:
- Sub-case max = kadBestMax: Same as Case 1 achievability.
- Sub-case max = psum - kadBestMin (and psum - kadBestMin > kadBestMax): By bestMin_short_witness, ∃ s l with s+l ≤ n, 1 ≤ l, l < n, linSum = kadBestMin. Take start = (s+l) % n = s+l (since s+l < n because s+l ≤ n and we can check), len = n - l. Or more precisely: the complementary circular subarray has start = s+l (if s+l < n) or 0 (if s+l = n... but l < n means s+l ≤ n and if s+l = n then start = 0). The complement wraps if s+l > 0 and start+len = s+l + (n-l) = s+n > n (when s > 0) or = n (when s = 0, non-wrapping). In either case, circSegmentSum of the complement = psum - linSum(s, l) = psum - kadBestMin. So we can take the complement as our witness. Actually, for the non-wrapping complement case (s = 0): start = l, len = n - l. start + len = l + n - l = n ≤ n. It's non-wrapping. circSegmentSum = linSum(l, n-l). And psum = linSum(0, l) + linSum(l, n-l), so linSum(l, n-l) = psum - linSum(0, l) = psum - kadBestMin. ✓
  For wrapping (s > 0): start = s+l, len = n-l. start < n (since s+l ≤ n, and if s+l = n then start = 0, but s > 0 so s+l > l ≥ 1, hence start ≥ 1. If s+l = n, hmm that means start = n which is bad. But s+l ≤ n from the witness, so start = s+l ≤ n. If s+l = n, we need to handle this. Actually if s + l = n and s > 0, then take start = 0, len = n - l. This is non-wrapping (start + len = n - l ≤ n). circSeg = linSum(0, n-l). And linSum(0, n) = linSum(0, n-l) + linSum(n-l, l). Since s+l = n means s = n-l, so linSum(n-l, l) = linSum(s, l) = kadBestMin. Hence linSum(0, n-l) = psum - kadBestMin. ✓

  General approach: take start' = (s + l) mod n, len' = n - l. Then circSegmentSum(start', len') = psum - linSum(s, l) = psum - kadBestMin.

Maximality:
- Non-wrapping: circSegmentSum = linSum ≤ kadBestMax ≤ max(kadBestMax, psum - kadBestMin) = result. (By kadBestMax_upper and circSeg_nonwrap.)
- Wrapping: circSegmentSum = psum - linSum(gap). gap is valid linear, so linSum(gap) ≥ kadBestMin (by kadBestMin_lower). Hence circSegmentSum ≤ psum - kadBestMin ≤ max(kadBestMax, psum - kadBestMin) = result. (By circSeg_wrap.)

Unfold postcondition and implementation. Split into achievability (∃) and maximality (∀).

The precondition gives hn : nums.size > 0, so the if nums.size = 0 branch is not taken.

Step 0: Characterize the implementation output.
Use go_result to get: the go function returns (psum nums n, kadBestMax(n-1), kadBestMin(n-1)).
So implementation nums = if kadBestMax(n-1) < 0 then kadBestMax(n-1) else max(kadBestMax(n-1), psum(n) - kadBestMin(n-1)).

**Case 1: kadBestMax(n-1) < 0**
Result = kadBestMax(n-1).

Achievability: By kadBestMax_achieved, ∃ s l with s+l ≤ n, 1 ≤ l, linSum s l = kadBestMax(n-1). This is a valid non-wrapping circular segment (start = s, len = l, isValidCircSegment holds with s < n from s+l ≤ n and l ≥ 1). By circSeg_nonwrap, circSegmentSum = linSum = kadBestMax = result.

Maximality: For any valid (start, len):
- If start + len ≤ n: circSegmentSum = linSum (by circSeg_nonwrap) ≤ kadBestMax (by kadBestMax_upper) = result.
- If start + len > n: use wrap_le_kadBestMax_neg with hallneg = all_neg_of_kadBestMax_neg.

**Case 2: ¬(kadBestMax(n-1) < 0), i.e., kadBestMax(n-1) ≥ 0**
Result = max(kadBestMax(n-1), psum(n) - kadBestMin(n-1)).

Achievability: Use max_cases to split.
- If result = kadBestMax(n-1): same as Case 1 achievability.
- If result = psum(n) - kadBestMin(n-1) > kadBestMax(n-1):
  By bestMin_short_witness, ∃ s l with s+l ≤ n, 1 ≤ l, l < n, linSum = kadBestMin.
  The complement circular subarray: start' = (s+l) % n, len' = n - l.
  isValidCircSegment: start' < n (Nat.mod_lt), 1 ≤ len' = n-l (since l < n), len' ≤ n.
  If s+l < n: start' = s+l. start'+len' = s+l+n-l = s+n > n. So it wraps.
    By circSeg_wrap: circSegmentSum = psum(n) - linSum(start'+len'-n, n-len') = psum(n) - linSum(s+l+n-l-n, l) = psum(n) - linSum(s, l) = psum(n) - kadBestMin = result. ✓
  If s+l = n: start' = 0. len' = n-l. start'+len' = n-l ≤ n. Non-wrapping.
    circSegmentSum = linSum(0, n-l) (by circSeg_nonwrap).
    psum(n) = linSum(0, n) = linSum(0, n-l) + linSum(n-l, l).
    Since s=n-l, linSum(n-l, l) = linSum(s, l) = kadBestMin.
    So linSum(0, n-l) = psum(n) - kadBestMin = result. ✓

Maximality: For any valid (start, len):
- If start + len ≤ n: circSegmentSum = linSum ≤ kadBestMax ≤ max(kadBestMax, psum-kadBestMin) = result.
- If start + len > n: By circSeg_wrap, circSegmentSum = psum(n) - linSum(gap_start, gap_len) where gap_start = start+len-n, gap_len = n-len. The gap is a valid linear subarray (gap_start + gap_len = start < n ≤ n, gap_len ≥ 1 if len < n, or gap_len = 0 if len = n). If len = n: circSegmentSum = psum(n) ≤ kadBestMax (by kadBestMax_ge_psum) ≤ result. If len < n: linSum(gap) ≥ kadBestMin (by kadBestMin_lower, noting gap_start + gap_len = start < n ≤ n). So circSegmentSum ≤ psum - kadBestMin ≤ max(kadBestMax, psum-kadBestMin) = result.

Unfold `implementation`. The if nums.size = 0 branch is false since hn : 0 < nums.size. Use `simp [implementation, show ¬(nums.size = 0) from by omega]` to eliminate the first branch. Then the implementation becomes: let st := go 1 first first first first first; if st.2.1 < 0 then st.2.1 else max st.2.1 (st.1 - st.2.2). By go_result, st = (psum nums nums.size, kadBestMax nums (nums.size - 1), kadBestMin nums (nums.size - 1)). So implementation = if kadBestMax < 0 then kadBestMax else max kadBestMax (psum - kadBestMin). This exactly matches the target.
-/
lemma impl_eq_formula (nums : Array Int) (hn : 0 < nums.size) :
    implementation nums =
    if kadBestMax nums (nums.size - 1) < 0 then kadBestMax nums (nums.size - 1)
    else max (kadBestMax nums (nums.size - 1)) (psum nums nums.size - kadBestMin nums (nums.size - 1)) := by
  unfold implementation;
  -- Apply the go_result lemma to rewrite the go function's output.
  have h_go : implementation.go nums 1 (nums[0]!) (nums[0]!) (nums[0]!) (nums[0]!) (nums[0]!) = (psum nums nums.size, kadBestMax nums (nums.size - 1), kadBestMin nums (nums.size - 1)) := by
    exact?;
  grind

/-
PROBLEM
linSum splits: linSum 0 (a+b) = linSum 0 a + linSum a b

PROVIDED SOLUTION
Unfold linSum. We need: (Finset.range (a+b)).sum (fun j => nums[0+j]!) = (Finset.range a).sum (fun j => nums[0+j]!) + (Finset.range b).sum (fun j => nums[a+j]!). The LHS is a sum over [0, a+b). Split at a using Finset.sum_range_add (or Finset.sum_range_add_sum_Ico): sum over [0, a+b) = sum over [0, a) + sum over [a, a+b). The second part, after shifting indices, equals (Finset.range b).sum (fun j => nums[a+j]!). Use simp to simplify 0 + j = j.
-/
lemma linSum_split (nums : Array Int) (a b : Nat) :
    linSum nums 0 (a + b) = linSum nums 0 a + linSum nums a b := by
  unfold linSum; simp +decide [ add_assoc, Finset.sum_range_add ] ;

/-
PROBLEM
The complement of a short linear subarray achieves psum - linSum as a circular segment.

PROVIDED SOLUTION
Given s, l with s+l ≤ n, 1 ≤ l, l < n, we construct a circular segment with sum = psum - linSum(s, l).

Case 1: s + l < n.
  Take start = s + l, len = n - l.
  isValidCircSegment: hn ✓, start = s+l < n ✓, 1 ≤ n-l (since l < n) ✓, n-l ≤ n ✓.
  start + len = s + l + n - l = s + n.
  If s = 0: start + len = n, not wrapping (n ≤ n but need n < n for wrap, so non-wrapping).
    circSegmentSum = linSum(l, n-l) (by circSeg_nonwrap).
    By linSum_split: linSum 0 n = linSum 0 l + linSum l (n-l).
    And psum = linSum 0 n (by psum_eq_linSum_zero).
    Also linSum 0 l = linSum s l (since s = 0).
    So linSum(l, n-l) = psum - linSum(s, l). ✓
  If s > 0: start + len = s + n > n. Wraps.
    By circSeg_wrap: circSegmentSum = psum - linSum(s+l+n-l-n, n-(n-l)) = psum - linSum(s, l). ✓

Case 2: s + l = n.
  Take start = 0, len = n - l.
  isValidCircSegment: hn ✓, 0 < n ✓, 1 ≤ n-l ✓, n-l ≤ n ✓.
  start + len = n-l ≤ n. Non-wrapping.
  circSegmentSum = linSum(0, n-l) (by circSeg_nonwrap).
  Since s + l = n, s = n - l.
  By linSum_split: linSum 0 n = linSum 0 (n-l) + linSum (n-l) l.
  psum = linSum 0 n. linSum(n-l, l) = linSum(s, l).
  So linSum(0, n-l) = psum - linSum(s, l). ✓
-/
lemma complement_achieves (nums : Array Int) (s l : Nat)
    (hn : 0 < nums.size) (hsl : s + l ≤ nums.size) (hl1 : 1 ≤ l) (hlt : l < nums.size) :
    ∃ start len, isValidCircSegment nums start len ∧
    circSegmentSum nums start len = psum nums nums.size - linSum nums s l := by
  by_cases h_case : s + l < nums.size;
  · by_cases hs : s = 0 <;> simp_all +decide [isValidCircSegment];
    · use l, nums.size - l;
      simp_all +decide [ circSegmentSum, linSum, psum ];
      rw [ ← Finset.sum_range_add_sum_Ico _ hlt.le ];
      simp +decide [ add_comm l, Finset.sum_Ico_eq_sum_range ];
      exact ⟨ Nat.sub_pos_of_lt hlt, Finset.sum_congr rfl fun x hx => by rw [ Nat.mod_eq_of_lt ( by linarith [ Finset.mem_range.mp hx, Nat.sub_add_cancel hlt.le ] ) ] ⟩;
    · use s + l, nums.size - l;
      rw [ circSeg_wrap ];
      any_goals omega;
      grind;
  · use 0, nums.size - l, by
      exact ⟨ hn, by linarith, Nat.sub_pos_of_lt hlt, Nat.sub_le _ _ ⟩
    generalize_proofs at *;
    convert circSeg_nonwrap nums 0 ( nums.size - l ) hn _ using 1 <;> norm_num [ show s = nums.size - l by omega ];
    rw [ show linSum nums 0 ( nums.size - l ) = linSum nums 0 ( nums.size - l ) from rfl, show linSum nums ( nums.size - l ) l = linSum nums ( nums.size - l ) l from rfl, show psum nums nums.size = linSum nums 0 nums.size from psum_eq_linSum_zero nums ] ; rw [ show linSum nums 0 nums.size = linSum nums 0 ( nums.size - l ) + linSum nums ( nums.size - l ) l from ?_ ] ; ring;
    exact linSum_split _ _ _ ▸ by rw [ Nat.sub_add_cancel hlt.le ] ;

/-
PROBLEM
Achievability: the implementation output is achieved by some valid circular segment.

PROVIDED SOLUTION
Rewrite using impl_eq_formula. Split into cases.

Case 1: kadBestMax < 0. Result = kadBestMax.
  By kadBestMax_achieved, ∃ s l with s+l ≤ n, 1 ≤ l, linSum = kadBestMax.
  Take start = s, len = l.
  isValidCircSegment: hn ✓, s < n (s+l ≤ n, l ≥ 1 → s ≤ n-1) ✓, 1 ≤ l ✓, l ≤ n ✓.
  circSegmentSum = linSum (by circSeg_nonwrap since s+l ≤ n) = kadBestMax = result (since impl_eq_formula with kadBestMax < 0).

Case 2: kadBestMax ≥ 0.
  Result = max(kadBestMax, psum - kadBestMin).
  Sub-case 2a: kadBestMax ≥ psum - kadBestMin. result = kadBestMax. Same as Case 1.
  Sub-case 2b: psum - kadBestMin > kadBestMax. result = psum - kadBestMin.
    By bestMin_short_witness, ∃ s l with s+l ≤ n, 1 ≤ l, l < n, linSum = kadBestMin.
    By complement_achieves, ∃ start len, isValidCircSegment ∧ circSegmentSum = psum - linSum(s,l) = psum - kadBestMin.
    And result = max(kadBestMax, psum - kadBestMin) = psum - kadBestMin (since psum - kadBestMin > kadBestMax).
    So circSegmentSum = psum - kadBestMin = result. ✓
-/
lemma impl_achievable (nums : Array Int) (hn : 0 < nums.size) :
    ∃ start len, isValidCircSegment nums start len ∧
    circSegmentSum nums start len = implementation nums := by
  -- By definition of `implementation`, we know that it returns the maximum of `kadBestMax` and `psum - kadBestMin`.
  have h_impl_def : implementation nums = if kadBestMax nums (nums.size - 1) < 0 then kadBestMax nums (nums.size - 1) else max (kadBestMax nums (nums.size - 1)) (psum nums nums.size - kadBestMin nums (nums.size - 1)) := by
    exact?;
  split_ifs at h_impl_def;
  · obtain ⟨ s, l, hsl, hl1, h_eq ⟩ := kadBestMax_achieved nums hn;
    refine' ⟨ s, l, ⟨ hn, _, _, _ ⟩, _ ⟩ <;> try linarith;
    rw [ h_impl_def, circSeg_nonwrap nums s l hn hsl, h_eq ];
  · cases max_cases ( kadBestMax nums ( nums.size - 1 ) ) ( psum nums nums.size - kadBestMin nums ( nums.size - 1 ) ) <;> simp_all +decide only;
    · obtain ⟨ s, l, hsl, hl1, h_eq ⟩ := kadBestMax_achieved nums hn;
      refine' ⟨ s, l, ⟨ hn, _, _, _ ⟩, _ ⟩ <;> try linarith! [ Nat.sub_add_cancel hn ] ;
      rw [ ← h_eq, circSeg_nonwrap ] <;> aesop;
    · have := bestMin_short_witness nums hn ( by linarith ) ( by linarith );
      obtain ⟨ s, l, hsl₁, hsl₂, hsl₃, hsl₄ ⟩ := this; have := complement_achieves nums s l hn hsl₁ hsl₂ hsl₃; aesop;

/-
PROBLEM
Maximality: every valid circular segment has sum ≤ the implementation output.

PROVIDED SOLUTION
Rewrite using impl_eq_formula. Split into cases on kadBestMax < 0.

**Case 1: kadBestMax < 0 (all negative)**
Result = kadBestMax. For any valid (start, len):
- If start + len ≤ n (non-wrapping): circSegmentSum = linSum (by circSeg_nonwrap) ≤ kadBestMax (by kadBestMax_upper) = result.
- If start + len > n (wrapping): use wrap_le_kadBestMax_neg with hallneg from all_neg_of_kadBestMax_neg.

**Case 2: kadBestMax ≥ 0**
Result = max(kadBestMax, psum - kadBestMin).
- If start + len ≤ n: circSegmentSum = linSum ≤ kadBestMax ≤ max(...) = result. Use le_max_left.
- If start + len > n:
  - If len = n: The circular subarray covers all elements. circSegmentSum = sum of all n elements through the circular indices. Since each index (start+i) % n cycles through all n values exactly once, circSegmentSum = psum n. And psum ≤ kadBestMax ≤ result by kadBestMax_ge_psum. But to show circSegmentSum = psum when len = n, we need to be careful. Actually, when start + len > n and len = n: circSegmentSum nums start n. Each i in [0, n) gives (start + i) % n which is a permutation of [0, n). But Finset.sum over a permutation equals the original sum. Actually it's simpler: just use circSeg_nonwrap if start = 0 (start + n ≤ n iff start = 0 but we assumed start + len > n so start > 0). Hmm, if len = n and start > 0 then start + n > n. Use circSeg_wrap: circSegmentSum = psum - linSum(start+n-n, n-n) = psum - linSum(start, 0) = psum - 0 = psum. But circSeg_wrap requires nums.size < start + len which is nums.size < start + n, i.e., 0 < start. And it requires 1 ≤ len = n and len ≤ n. Wait, but the gap length is n - n = 0, and linSum with length 0 is an empty sum = 0. So it gives psum - 0 = psum. However circSeg_wrap also requires the gap to be valid which may need gap_len ≥ 1. Let me check: circSeg_wrap just states the formula, it doesn't require gap_len ≥ 1. Actually check: the statement says circSeg_wrap needs hwrap : nums.size < start + len. When len = n and start > 0, this holds. And the formula gives psum - linSum(start, 0) = psum - 0 = psum.

  Actually wait, does circSeg_wrap even apply when len = n? Let me check: it needs hn, hs (start < n), hl1 (1 ≤ len = n), hln (n ≤ n), hwrap (n < start + n). These all hold when start > 0 and n > 0. The gap_len = n - n = 0, so linSum(gap) = 0. circSegmentSum = psum - 0 = psum. ✓

  And psum ≤ kadBestMax (by kadBestMax_ge_psum) ≤ max(kadBestMax, ...) = result. ✓

  - If len < n: By circSeg_wrap, circSegmentSum = psum - linSum(gap_start, gap_len) where gap_start = start+len-n, gap_len = n-len ≥ 1. The gap is a valid linear subarray: gap_start + gap_len = start+len-n+n-len = start < n ≤ n, and gap_len = n-len ≥ 1. By kadBestMin_lower, linSum(gap) ≥ kadBestMin. So circSegmentSum = psum - linSum(gap) ≤ psum - kadBestMin ≤ max(kadBestMax, psum-kadBestMin) = result. Use le_max_right.
-/
lemma impl_maximal (nums : Array Int) (hn : 0 < nums.size) :
    ∀ start len, isValidCircSegment nums start len →
    circSegmentSum nums start len ≤ implementation nums := by
  intro start len h;
  by_cases hwrap : nums.size < start + len <;> simp_all +decide [ isValidCircSegment ];
  · by_cases hbm : kadBestMax nums (nums.size - 1) < 0 <;> simp_all +decide [ impl_eq_formula ];
    · apply wrap_le_kadBestMax_neg nums start len hn h.left h.right.left h.right.right hwrap (all_neg_of_kadBestMax_neg nums hn hbm);
    · by_cases hlen : len < nums.size <;> simp_all +decide [ circSeg_wrap ];
      · split_ifs <;> simp_all +decide [ le_of_lt ];
        · linarith;
        · refine' le_trans _ ( add_le_add ( le_max_right _ _ ) ( kadBestMin_lower _ _ _ _ ( by omega ) ( by omega ) ) ) ; norm_num [ psum_eq_linSum_zero ] ; omega;
      · split_ifs <;> simp_all +decide [ linSum ];
        · linarith;
        · exact Or.inl ( kadBestMax_ge_psum nums hn );
  · -- By definition of circSegmentSum, we have circSegmentSum nums start len = linSum nums start len.
    have h_circSeg : circSegmentSum nums start len = linSum nums start len := by
      exact circSeg_nonwrap nums start len hn hwrap |> fun x => x ▸ rfl;
    rw [ impl_eq_formula ];
    · split_ifs <;> simp_all +decide [ kadBestMax_upper ];
    · linarith

theorem correctness_goal_0_0 (nums : Array ℤ) (h_precond : precondition nums) : postcondition nums (implementation nums) := by
  exact ⟨impl_achievable nums h_precond, impl_maximal nums h_precond⟩

end Proof
