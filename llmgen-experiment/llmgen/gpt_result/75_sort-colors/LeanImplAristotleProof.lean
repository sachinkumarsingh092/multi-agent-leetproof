import Lean

import Mathlib

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    SortColors: Given an array of colors encoded as 0, 1, 2, reorder it so that all 0s come first,
    then all 1s, then all 2s.
    Natural language breakdown:
    1. The input is an array `nums` of natural numbers that represent colors.
    2. Only the values 0, 1, and 2 are valid colors.
    3. The output must have the same length as the input.
    4. The output must contain the same multiset of elements as the input (no loss/duplication).
    5. The output must be ordered so that every 0 appears before every 1 and every 1 before every 2.
    6. Equivalently, there exist boundaries a ≤ b such that indices < a are 0, indices in [a,b) are 1,
       and indices ≥ b are 2.
    Your algorithm should run in **O(n)** time and **O(1)** extra space (in-place).
-/

-- Helper: all entries are in {0,1,2}
def ColorsOnly (nums : Array Nat) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≤ 2

-- Helper: array is partitioned into 0s then 1s then 2s
-- This avoids referencing any particular algorithm while fully characterizing the desired order.
def Is012Sorted (nums : Array Nat) : Prop :=
  ∃ (a : Nat) (b : Nat),
    a ≤ b ∧ b ≤ nums.size ∧
    (∀ (i : Nat), i < a → nums[i]! = 0) ∧
    (∀ (i : Nat), a ≤ i ∧ i < b → nums[i]! = 1) ∧
    (∀ (i : Nat), b ≤ i ∧ i < nums.size → nums[i]! = 2)

-- Helper: count occurrences of a value in an array
-- (Array.count is available when DecidableEq is available.)
def countVal (nums : Array Nat) (v : Nat) : Nat :=
  nums.count v

-- Preconditions: input must contain only 0/1/2.
def precondition (nums : Array Nat) : Prop :=
  ColorsOnly nums

-- Postconditions: result has same size, is ordered as 0-then-1-then-2,
-- and preserves the counts of 0,1,2 from the input.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  result.size = nums.size ∧
  Is012Sorted result ∧
  countVal result 0 = countVal nums 0 ∧
  countVal result 1 = countVal nums 1 ∧
  countVal result 2 = countVal nums 2
end Specs

section Impl
def implementation (nums : Array Nat) : Array Nat :=
  -- Use a single pass to count 0/1/2, then overwrite the input array in place
  -- by setting each index accordingly. This uses O(1) extra space (besides the
  -- output array itself) and O(n) time.
  let (c0, c1, c2) :=
    nums.foldl
      (fun (acc : Nat × Nat × Nat) x =>
        let (c0, c1, c2) := acc
        if x = 0 then (c0 + 1, c1, c2)
        else if x = 1 then (c0, c1 + 1, c2)
        else (c0, c1, c2 + 1))
      (0, 0, 0)
  let n := nums.size

  let rec fill (a : Array Nat) (i : Nat) : Array Nat :=
    if h : i < n then
      let v :=
        if i < c0 then 0
        else if i < c0 + c1 then 1
        else 2
      fill (a.set! i v) (i + 1)
    else
      a
  termination_by n - i

  fill nums 0
end Impl

section TestCases
-- Test case 1: Example 1 from the problem statement
-- Input: [2,0,2,1,1,0] Output: [0,0,1,1,2,2]
def test1_nums : Array Nat := #[2, 0, 2, 1, 1, 0]
def test1_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 2: Example 2 from the problem statement
-- Input: [2,0,1] Output: [0,1,2]
def test2_nums : Array Nat := #[2, 0, 1]
def test2_Expected : Array Nat := #[0, 1, 2]

-- Test case 3: Empty array (degenerate but valid)
def test3_nums : Array Nat := #[]
def test3_Expected : Array Nat := #[]

-- Test case 4: Singleton 0
def test4_nums : Array Nat := #[0]
def test4_Expected : Array Nat := #[0]

-- Test case 5: Singleton 1
def test5_nums : Array Nat := #[1]
def test5_Expected : Array Nat := #[1]

-- Test case 6: Singleton 2
def test6_nums : Array Nat := #[2]
def test6_Expected : Array Nat := #[2]

-- Test case 7: Already sorted with repeats
def test7_nums : Array Nat := #[0, 0, 1, 1, 2, 2]
def test7_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 8: Reverse sorted
def test8_nums : Array Nat := #[2, 2, 1, 1, 0, 0]
def test8_Expected : Array Nat := #[0, 0, 1, 1, 2, 2]

-- Test case 9: Mixed small (extra diversity)
def test9_nums : Array Nat := #[1, 0, 2, 0, 1]
def test9_Expected : Array Nat := #[0, 0, 1, 1, 2]

-- Recommend to validate: precondition, postcondition, SortColors
end TestCases

section Proof

-- Helper: unfolding lemma for implementation.fill
theorem fill_unfold (c0 c1 n : ℕ) (a : Array ℕ) (i : ℕ) :
    implementation.fill c0 c1 n a i =
      if i < n then
        implementation.fill c0 c1 n (a.set! i (if i < c0 then 0 else if i < c0 + c1 then 1 else 2)) (i + 1)
      else a := by
  rw [implementation.fill]
  split <;> rfl

/-
PROBLEM
Base case: when all positions are filled, the array equals the target

PROVIDED SOLUTION
Use Array.ext to show both arrays are equal element-wise. The sizes match: a.size = n = c0+c1+c2, and (replicate c0 0 ++ replicate c1 1 ++ replicate c2 2).size = c0+c1+c2.

For each index j < n, show a[j]! equals the j-th element of the concatenation:
- if j < c0: a[j]! = 0 by h_all, and the concat has value 0 (from the first replicate)
- if c0 ≤ j < c0+c1: a[j]! = 1 by h_all, and the concat has value 1
- if c0+c1 ≤ j: a[j]! = 2 by h_all, and the concat has value 2

Use getElem!_pos to convert getElem! to getElem, and Array.getElem_append, Array.getElem_replicate for the concatenation.
-/
theorem fill_base_case (c0 c1 c2 n : ℕ) (h_sum : c0 + c1 + c2 = n)
    (a : Array ℕ) (ha : a.size = n)
    (h_all : ∀ j, j < n → a[j]! = if j < c0 then 0 else if j < c0 + c1 then 1 else 2) :
    a = Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2 := by
  grind

/-
PROBLEM
Prefix preservation: set! at index i preserves values at indices < i

PROVIDED SOLUTION
Unfold set! to setIfInBounds, then use Array.getElem_setIfInBounds or similar lemma showing that setting at index i doesn't affect index j when j ≠ i. Since j < i, j ≠ i, so the value is unchanged.
-/
theorem set_bang_prefix (a : Array ℕ) (i j : ℕ) (v : ℕ) (hj : j < i) (hi : i < a.size) :
    (a.set! i v)[j]! = a[j]! := by
  grind

/-
PROBLEM
The main inductive lemma

Helper for the prefix condition in the inductive step

PROVIDED SOLUTION
By induction on (n - i). Use `induction' h : n - i with d ih generalizing i a`.

Base case (n - i = 0, i.e., i = n): Use fill_unfold. Since ¬(i < n), fill returns a. Then apply fill_base_case using h_prefix (with i = n, so all j < n are covered).

Inductive case (n - i = d + 1, so i < n): Use fill_unfold. Since i < n, fill becomes fill(a.set! i v, i+1). Apply ih with (a.set! i v) and (i+1). Verify:
- (a.set! i v).size = n: by Array.size_set! or simp
- i + 1 ≤ n: from i < n
- n - (i+1) = d: from h
- prefix condition for i+1: for j < i, use set_bang_prefix to show (a.set! i v)[j]! = a[j]! and then h_prefix. For j = i, (a.set! i v)[i]! = v which is exactly the if-expression.

Use set_bang_prefix and fill_base_case as named helper lemmas.

By induction on (n - i). Use `induction' d : n - i with d ih generalizing i a`.

Base case (n - i = 0, so i ≥ n): Use fill_unfold and if_neg. Since i ≤ n and n - i = 0, we have i = n. fill returns a. Apply fill_base_case.

Inductive case (n - i = d + 1, so i < n): Use fill_unfold and if_pos. fill becomes fill(a.set! i v, i+1). Apply ih. Check:
- size: Array.size_set! gives (a.set! i v).size = a.size = n
- bound: i + 1 ≤ n from i < n
- n - (i+1) = d from hypothesis
- prefix for i+1: for j < i, use set_bang_prefix; for j = i, need (a.set! i v)[i]! = v

For the last part (j = i), key facts:
- set! when i < a.size is just a.set i v h, so (a.set! i v)[i]! can be simplified
- Use Array.set!_eq_setIfInBounds, Array.setIfInBounds, and getElem!/getElem conversion

IMPORTANT: Do NOT use `grind +locals` or `grind +qlia` or `grind +ring` - they don't exist in this Lean version (4.24.0). Only plain `grind` works. Prefer `simp`, `omega`, `split_ifs`, `rw`, `exact` tactics.

For j < i + 1, either j < i or j = i.

Case j < i: We need (a.setIfInBounds i v)[j]! = a[j]!. Since j ≠ i, setIfInBounds at i doesn't change index j. Use Array.setIfInBounds, dif_pos (show i < a.size from ha and hi), then Array.getElem_set with i ≠ j. Then apply h_prefix.

Case j = i: We need (a.setIfInBounds i v)[i]! = v. Unfold setIfInBounds, use dif_pos, then show (a.set i v _)[i]! = v using Array.getElem_set with i = i.

For getElem! to getElem conversion, use the fact that the array size is preserved by setIfInBounds.

IMPORTANT: Do NOT use `grind +locals`, `grind +qlia`, or `grind +ring`. Only plain `grind` or preferably `simp`, `omega`, `split_ifs`.
-/
theorem prefix_extend (c0 c1 n : ℕ) (a : Array ℕ) (i : ℕ) (ha : a.size = n) (hi : i < n)
    (h_prefix : ∀ j, j < i → a[j]! = if j < c0 then 0 else if j < c0 + c1 then 1 else 2) :
    ∀ j, j < i + 1 →
      (a.setIfInBounds i (if i < c0 then 0 else if i < c0 + c1 then 1 else 2))[j]! =
        if j < c0 then 0 else if j < c0 + c1 then 1 else 2 := by
  grind

theorem fill_inductive (c0 c1 c2 n : ℕ) (h_sum : c0 + c1 + c2 = n)
    (a : Array ℕ) (i : ℕ) (ha : a.size = n) (hi : i ≤ n)
    (h_prefix : ∀ j, j < i → a[j]! = if j < c0 then 0 else if j < c0 + c1 then 1 else 2) :
    implementation.fill c0 c1 n a i =
      Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2 := by
  -- We proceed by induction on the difference between n and i.
  induction' h : n - i with d ih generalizing i a;
  · rw [ Nat.sub_eq_iff_eq_add ] at h;
    · convert fill_base_case c0 c1 c2 n h_sum a ha _ using 1;
      · unfold implementation.fill; aesop;
      · intro j hj; exact h_prefix j (by omega)
    · linarith;
  · rw [ fill_unfold, if_pos ];
    · convert ih ( a.setIfInBounds i ( if i < c0 then 0 else if i < c0 + c1 then 1 else 2 ) ) ( i + 1 ) ?_ ?_ ?_ ?_ using 1;
      · rw [ Array.size_setIfInBounds ] ; aesop;
      · omega;
      · exact prefix_extend c0 c1 n a i ha (by omega) h_prefix
      · omega;
    · omega

theorem correctness_goal_4 (nums : Array ℕ) (h_precond : precondition nums) (counts : ℕ × ℕ × ℕ) (hcounts : counts =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 => if x = 0 then (c0 + 1, c1, c2) else if x = 1 then (c0, c1 + 1, c2) else (c0, c1, c2 + 1)) fst
            fst_1 snd)
    (0, 0, 0) nums) (c0 : ℕ) (c1 : ℕ) (c2 : ℕ) (hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2)) (n : ℕ) (hn : n = nums.size) (h_count0 : c0 = Array.count 0 nums) (h_count1 : c1 = Array.count 1 nums) (h_count2 : c2 = Array.count 2 nums) (h_sum : c0 + c1 + c2 = n) : implementation.fill c0 c1 n nums 0 = Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2 := by
    exact fill_inductive c0 c1 c2 n h_sum nums 0 (by omega) (by omega) (by intro j hj; omega)
end Proof