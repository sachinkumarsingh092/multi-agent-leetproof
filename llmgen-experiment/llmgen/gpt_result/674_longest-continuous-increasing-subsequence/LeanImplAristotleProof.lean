/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 279b40c3-6fc4-492f-a04d-09d90d64344b

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
    674. Longest Continuous Increasing Subsequence: return the length of the longest strictly increasing contiguous subarray.
    **Important: complexity should be O(n) time and O(1) space**
    Natural language breakdown:
    1. Input is an array of integers `nums`.
    2. A continuous subsequence is a contiguous subarray determined by a start index `l` and a positive length `len`.
    3. Such a subarray is strictly increasing when each adjacent pair increases: for all valid offsets `i`,
       nums[l+i] < nums[l+i+1].
    4. The output is the maximum length among all strictly increasing contiguous subarrays.
    5. Since a single element is trivially strictly increasing, when the array is non-empty the answer is at least 1.
-/

-- A segment starting at `l` with length `len` is within bounds.
def segInBounds (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  l + len ≤ nums.size

-- A segment is required to be non-empty.
def segNonempty (len : Nat) : Prop :=
  1 ≤ len

-- Strictly increasing adjacent condition over a bounded, non-empty segment.
def segStrictlyIncreasing (nums : Array Int) (l : Nat) (len : Nat) : Prop :=
  segNonempty len ∧
  segInBounds nums l len ∧
  (∀ (i : Nat), i + 1 < len → nums[l + i]! < nums[l + i + 1]!)

-- Precondition: we follow the common problem constraint that the input array is non-empty.
def precondition (nums : Array Int) : Prop :=
  nums.size > 0

-- Postcondition: result is exactly the maximum length of any strictly increasing contiguous segment.
def postcondition (nums : Array Int) (result : Nat) : Prop :=
  result ≥ 1 ∧
  result ≤ nums.size ∧
  (∃ (l : Nat), segStrictlyIncreasing nums l result) ∧
  (∀ (l : Nat) (len : Nat), segStrictlyIncreasing nums l len → len ≤ result)

end Specs

section Impl

def implementation (nums : Array Int) : Nat :=
  -- O(n) time, O(1) extra space: single pass tracking current run length and best.
  let n := nums.size
  if h0 : n = 0 then
    0
  else
    let rec go (i : Nat) (cur best : Nat) : Nat :=
      if h : i < n then
        -- compare nums[i-1] and nums[i]
        let prev := nums[i-1]!
        let x := nums[i]!
        let cur' := if prev < x then cur + 1 else 1
        let best' := Nat.max best cur'
        go (i + 1) cur' best'
      else
        best
    termination_by n - i
    -- start from i=1 with cur=1 best=1
    go 1 1 1

end Impl

section TestCases

-- Test case 1: Example 1
-- nums = [1,3,5,4,7] => longest increasing contiguous subarray is [1,3,5], length 3
def test1_nums : Array Int := #[1, 3, 5, 4, 7]

def test1_Expected : Nat := 3

-- Test case 2: Example 2
-- nums = [2,2,2,2,2] => any strictly increasing contiguous subarray has length 1
def test2_nums : Array Int := #[2, 2, 2, 2, 2]

def test2_Expected : Nat := 1

-- Test case 3: Entire array strictly increasing
def test3_nums : Array Int := #[1, 2, 3, 4]

def test3_Expected : Nat := 4

-- Test case 4: Strictly decreasing array
def test4_nums : Array Int := #[4, 3, 2, 1]

def test4_Expected : Nat := 1

-- Test case 5: Single element
def test5_nums : Array Int := #[10]

def test5_Expected : Nat := 1

-- Test case 6: Includes negative numbers and increasing through zero
def test6_nums : Array Int := #[-3, -2, -1, 0]

def test6_Expected : Nat := 4

-- Test case 7: Increase, then drop, then longer increase
def test7_nums : Array Int := #[1, 3, 2, 4, 5]

def test7_Expected : Nat := 3

-- Test case 8: Equal adjacent elements break strict increase
def test8_nums : Array Int := #[1, 2, 2, 3]

def test8_Expected : Nat := 2

-- Test case 9: Multiple runs, longest at end
def test9_nums : Array Int := #[0, 1, 0, 1, 2, 3]

def test9_Expected : Nat := 4

end TestCases

section Proof

noncomputable section AristotleLemmas

/-
Helper definitions L and M representing the length of the longest increasing suffix and the max increasing subarray length up to index i. Also impl_go which mirrors the implementation loop.
-/
def L (nums : Array Int) : Nat → Nat
| 0 => 0
| i+1 =>
  if i = 0 then 1
  else
    if nums[i-1]! < nums[i]! then L nums i + 1 else 1

def M (nums : Array Int) : Nat → Nat
| 0 => 0
| i+1 => Nat.max (M nums i) (L nums (i+1))

def impl_go (nums : Array Int) (n : Nat) (i : Nat) (cur : Nat) (best : Nat) : Nat :=
  if h : i < n then
    let prev := nums[i-1]!
    let x := nums[i]!
    let cur' := if prev < x then cur + 1 else 1
    let best' := Nat.max best cur'
    impl_go nums n (i + 1) cur' best'
  else
    best
termination_by n - i

lemma L_properties (nums : Array Int) : (∀ i, i > 0 → L nums i ≥ 1) ∧ (∀ i, L nums i ≤ i) := by
  constructor;
  · unfold L; aesop;
  · intro i
    induction' i with i ih;
    · exact?;
    · unfold L; aesop;

/-
L nums i returns the length of the longest strictly increasing contiguous subarray ending at index i-1. This lemma proves that the segment defined by L is indeed strictly increasing.
-/
lemma L_valid (nums : Array Int) (i : Nat) (h : i ≤ nums.size) (h_pos : i > 0) :
  segStrictlyIncreasing nums (i - L nums i) (L nums i) := by
    refine' ⟨ _, _, _ ⟩;
    · exact L_properties nums |>.1 i h_pos;
    · exact Nat.sub_add_cancel ( show L nums i ≤ i from by linarith [ L_properties nums |>.2 i ] ) |> fun x => x.le.trans h;
    · induction' i with i ih;
      · grind;
      · by_cases hi : i = 0 <;> simp_all +decide [ L ];
        split_ifs <;> simp_all +decide [ Nat.succ_sub ];
        intro j hj; specialize ih ( Nat.le_of_succ_le h ) ( Nat.pos_of_ne_zero hi ) j; rcases eq_or_lt_of_le hj.nat_succ_le with h' | h' <;> simp_all +decide [ Nat.sub_add_comm ] ;
        convert ‹nums[i - 1]! < nums[i]!› using 2 <;> norm_num [ ← h', Nat.sub_add_comm ( show L nums i ≤ i from L_properties nums |>.2 i ) ];
        · rw [ tsub_add_eq_add_tsub ];
          · omega;
          · linarith [ L_properties nums |>.2 i ];
        · linarith [ Nat.sub_add_cancel ( show j + 1 ≤ i from by linarith [ L_properties nums |>.2 i ] ) ]

/-
L nums i is the length of the longest strictly increasing contiguous subarray ending at index i-1. This lemma states that any such strictly increasing subarray ending at i-1 must have length at most L nums i.
-/
lemma L_maximal (nums : Array Int) (i : Nat) (len : Nat) (h : i ≤ nums.size)
  (h_len : len ≤ i)
  (h_seg : segStrictlyIncreasing nums (i - len) len) : len ≤ L nums i := by
    -- By definition of $L$, we know that $L nums i$ is the length of the longest strictly increasing subarray ending at index $i-1$.
    have h_L_def : ∀ (i : ℕ) (h : i ≤ nums.size), i > 0 → L nums i = if i = 1 then 1 else if nums[i - 2]! < nums[i - 1]! then L nums (i - 1) + 1 else 1 := by
      intro i hi hi'; rcases i with ( _ | _ | i ) <;> aesop;
    induction' len with len ih generalizing i <;> simp_all +decide;
    rcases i with ( _ | _ | i ) <;> simp_all +arith +decide [ Nat.sub_sub ];
    split_ifs <;> simp_all +arith +decide [ segStrictlyIncreasing ];
    · contrapose! ih;
      refine' ⟨ i + 1, by linarith, by linarith, _, _, _, _ ⟩ <;> simp_all +arith +decide [ segNonempty, segInBounds ];
      · grind;
      · grind;
      · exact fun n hn => h_seg n ( by linarith );
    · contrapose! h_seg;
      intro h1 h2; use len - 1; rcases len <;> simp_all +arith +decide;

/-
M nums i is the maximum length of a strictly increasing subarray ending at or before index i. This lemma proves that such a subarray actually exists.
-/
lemma M_valid (nums : Array Int) (i : Nat) (h : i ≤ nums.size) (h_pos : i > 0) :
  ∃ l, segStrictlyIncreasing nums l (M nums i) ∧ l + M nums i ≤ i := by
    induction' i with i ih <;> simp_all +decide [ M ];
    by_cases hi : 0 < i <;> simp_all +decide [ Nat.max_def ];
    · split_ifs;
      · exact ⟨ i + 1 - L nums ( i + 1 ), L_valid nums ( i + 1 ) ( by linarith ) ( by linarith ), by rw [ Nat.sub_add_cancel ( by linarith [ L_properties nums |>.2 ( i + 1 ) ] ) ] ⟩;
      · exact Exists.elim ( ih ( Nat.le_of_succ_le h ) ) fun l hl => ⟨ l, hl.1, by linarith ⟩;
    · use 0; split_ifs <;> simp_all +decide [ M, L ] ;
      constructor <;> norm_num [ segNonempty, segInBounds ] ; linarith!;

/-
M nums i is the maximum length of any strictly increasing subarray ending at or before index i. This lemma proves that any such subarray has length at most M nums i.
-/
lemma M_maximal (nums : Array Int) (i : Nat) (l len : Nat)
  (h_i : i ≤ nums.size)
  (h_seg : segStrictlyIncreasing nums l len) (h_bound : l + len ≤ i) : len ≤ M nums i := by
    induction' i with i ih generalizing l len;
    · aesop;
    · by_cases h_case : l + len ≤ i;
      · exact le_trans ( ih l len ( by linarith ) h_seg h_case ) ( by exact Nat.le_max_left _ _ );
      · -- Since $l + len = i + 1$, we have $len = i + 1 - l$. By Lemma L_maximal, $len \leq L nums (i + 1)$.
        have h_len_le_L : len ≤ L nums (i + 1) := by
          apply L_maximal;
          · linarith;
          · linarith;
          · convert h_seg using 1 ; omega;
        exact le_trans h_len_le_L ( Nat.le_max_right _ _ )

/-
The helper function `impl_go` correctly computes `M nums n` when started with the correct invariants.
-/
lemma impl_go_correct (nums : Array Int) (n : Nat) (i : Nat) (cur best : Nat)
  (hn : n = nums.size) (hi : i ≤ n) (hi_pos : i ≥ 1)
  (hcur : cur = L nums i) (hbest : best = M nums i) :
  impl_go nums n i cur best = M nums n := by
    -- We'll use induction on `n - i`.
    induction' h : n - i with d hd generalizing i cur best;
    · unfold impl_go;
      grind;
    · convert hd ( i + 1 ) ( L nums ( i + 1 ) ) ( Nat.max ( M nums i ) ( L nums ( i + 1 ) ) ) _ _ _ _ _ using 1;
      any_goals omega;
      · rw [ impl_go ];
        rcases i <;> simp_all +decide [ L ];
        grind;
      · exact?

/-
The implementation computes exactly `M nums nums.size`.
-/
lemma implementation_eq_M (nums : Array Int) (h : precondition nums) :
  implementation nums = M nums nums.size := by
    obtain ⟨n, hn⟩ : ∃ n, nums.size = n + 1 := by
      exact Nat.exists_eq_succ_of_ne_zero h.ne';
    rw [ hn, implementation ];
    convert impl_go_correct nums ( n + 1 ) 1 1 1 _ _ _ _ _ using 1;
    all_goals norm_num [ hn, L, M ];
    -- By definition of `go`, we can rewrite it using the recursive function `impl_go`.
    have h_go_eq_impl_go : ∀ (n : ℕ) (i : ℕ) (cur best : ℕ), i ≤ n → (implementation.go nums n i cur best) = (impl_go nums n i cur best) := by
      intros n i cur best hi
      induction' hi : n - i using Nat.strong_induction_on with k ih generalizing i cur best;
      unfold implementation.go impl_go;
      grind;
    exact h_go_eq_impl_go _ _ _ _ ( Nat.le_add_left _ _ )

end AristotleLemmas

theorem correctness_goal (nums : Array Int) (h_precond : precondition nums) : postcondition nums (implementation nums) := by
    rw [ implementation_eq_M _ h_precond ];
    refine' ⟨ _, _, _, _ ⟩;
    · obtain ⟨l, hl⟩ := M_valid nums nums.size (by
      rfl) (by
      exact h_precond);
      exact hl.1.1;
    · -- By definition of `M`, we know that `M nums i ≤ i` for all `i`.
      have hM_le_i : ∀ i, i ≤ nums.size → M nums i ≤ i := by
        intro i hi;
        induction' i with i ih;
        · rfl;
        · exact max_le ( le_trans ( ih ( Nat.le_of_succ_le hi ) ) ( Nat.le_succ _ ) ) ( L_properties nums |>.2 _ );
      exact hM_le_i _ le_rfl;
    · exact M_valid _ _ le_rfl h_precond |> fun ⟨ l, hl1, hl2 ⟩ => ⟨ l, hl1 ⟩;
    · intro l len h_seq
      have h_bound : l + len ≤ nums.size := by
        exact h_seq.2.1;
      exact M_maximal nums _ _ _ ( by linarith ) h_seq h_bound

end Proof