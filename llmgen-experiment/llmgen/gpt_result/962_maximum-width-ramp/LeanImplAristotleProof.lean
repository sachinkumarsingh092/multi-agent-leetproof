/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 094934d2-ae91-48e1-abe8-10d4d70e5856

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem correctness_goal_0 (nums : Array ℤ) (h_precond : precondition nums) (n : ℕ) (hsmall : n ≤ 1) (himpl : implementation nums = 0) (w : ℕ) (hw : IsRampWidth nums w) : ¬IsRampWidth nums w

- theorem correctness_goal_2_0 (nums : Array ℤ) (h_precond : precondition nums) (n : ℕ) (hsmall : ¬n ≤ 1) (himpl : implementation nums = implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0) (w : ℕ) (hw : IsRampWidth nums w) (hs : ¬nums.size ≤ 1) : ∀ (w : ℕ),
  IsRampWidth nums w →
    w ≤ implementation.scanRight nums nums.size (nums.size - 1) (implementation.buildStack nums nums.size 0 []) 0
-/

import Lean

import Mathlib.Tactic


set_option maxHeartbeats 10000000

section Specs

-- Never add new imports here

set_option maxHeartbeats 10000000

set_option pp.coercions false

/- Problem Description
    MaximumWidthRamp: compute the maximum width of a ramp in an integer array.
    Natural language breakdown:
    1. The input is an array `nums` of integers.
    2. A ramp is a pair of indices (i, j) such that i < j and nums[i] ≤ nums[j].
    3. The width of a ramp (i, j) is the natural number j - i.
    4. The goal is to return the maximum width among all ramps in the array.
    5. If there is no ramp (i.e., no pair i < j with nums[i] ≤ nums[j]), the result must be 0.
    6. The result is always between 0 and nums.size - 1.
    Your algorithm should run in **O(n)** time and **O(n)** extra space.
-/

-- A ramp predicate over indices of an array.
-- We use Nat indices and guard access with bounds.
def IsRamp (nums : Array Int) (i : Nat) (j : Nat) : Prop :=
  i < j ∧ j < nums.size ∧ nums[i]! ≤ nums[j]!

-- The set of all achievable ramp widths.
def IsRampWidth (nums : Array Int) (w : Nat) : Prop :=
  ∃ (i : Nat) (j : Nat), IsRamp nums i j ∧ w = j - i

-- Precondition: no special restrictions; empty and singleton arrays are allowed.
def precondition (nums : Array Int) : Prop :=
  True

-- Postcondition: result is the maximum achievable ramp width; if none exist, it is 0.
-- We avoid defining the result as a call to a reference implementation.
def postcondition (nums : Array Int) (result : Nat) : Prop :=
  (result = 0 ∨ IsRampWidth nums result) ∧
  (∀ (w : Nat), IsRampWidth nums w → w ≤ result)

end Specs

section Impl

def implementation (nums : Array Int) : Nat :=
  let n := nums.size
  if hsmall : n ≤ 1 then
    0
  else
    -- Build a stack of indices with strictly decreasing values (by nums[i]).
    let rec buildStack (i : Nat) (st : List Nat) : List Nat :=
      if h : i < n then
        let x := nums[i]!
        match st with
        | [] => buildStack (i + 1) [i]
        | j :: _ =>
          if x < nums[j]! then
            buildStack (i + 1) (i :: st)
          else
            buildStack (i + 1) st
      else
        st
    termination_by n - i

    -- Pop from stack while it forms a ramp with j, updating best.
    let rec popWhile (j : Nat) (st : List Nat) (best : Nat) : List Nat × Nat :=
      match st with
      | [] => ([], best)
      | i :: rest =>
        if nums[i]! ≤ nums[j]! then
          popWhile j rest (Nat.max best (j - i))
        else
          (st, best)
    termination_by st

    -- Scan from right to left.
    let rec scanRight (j : Nat) (st : List Nat) (best : Nat) : Nat :=
      if hj : j < n then
        let (st', best') := popWhile j st best
        match j with
        | 0 => best'
        | j' + 1 => scanRight j' st' best'
      else
        best
    termination_by j

    let st := buildStack 0 []
    scanRight (n - 1) st 0

end Impl

section TestCases

-- Test case 1: Example 1 from the prompt
-- nums = [6,0,8,2,1,5] → 4
-- (i, j) = (1, 5) gives width 4.
def test1_nums : Array Int := #[6, 0, 8, 2, 1, 5]

def test1_Expected : Nat := 4

-- Test case 2: Example 2 from the prompt
-- nums = [9,8,1,0,1,9,4,0,4,1] → 7
-- (i, j) = (2, 9) gives width 7.
def test2_nums : Array Int := #[9, 8, 1, 0, 1, 9, 4, 0, 4, 1]

def test2_Expected : Nat := 7

-- Test case 3: Empty array (degenerate)
def test3_nums : Array Int := #[]

def test3_Expected : Nat := 0

-- Test case 4: Singleton array (degenerate)
def test4_nums : Array Int := #[42]

def test4_Expected : Nat := 0

-- Test case 5: Strictly decreasing, no ramp exists
-- [5,4,3,2,1] has no i<j with nums[i] ≤ nums[j].
def test5_nums : Array Int := #[5, 4, 3, 2, 1]

def test5_Expected : Nat := 0

-- Test case 6: All equal values, widest ramp is first to last
-- size 4 → width 3.
def test6_nums : Array Int := #[7, 7, 7, 7]

def test6_Expected : Nat := 3

-- Test case 7: Strictly increasing, widest ramp is first to last
-- [1,2,3,4,5] → width 4.
def test7_nums : Array Int := #[1, 2, 3, 4, 5]

def test7_Expected : Nat := 4

-- Test case 8: Contains negative values
-- [-3,-2,-5,-1] max width ramp is (0,3): -3 ≤ -1 → width 3.
def test8_nums : Array Int := #[-3, -2, -5, -1]

def test8_Expected : Nat := 3

-- Test case 9: Multiple candidates; best uses a small left value far left
-- [2,1,2,0,1] best is (1,4): 1 ≤ 1 width 3.
def test9_nums : Array Int := #[2, 1, 2, 0, 1]

def test9_Expected : Nat := 3

end TestCases

section Proof

noncomputable section AristotleLemmas

/-
Auxiliary definition for `buildStack` lifted to the top level.
-/
def buildStack_aux (nums : Array Int) (n : Nat) (i : Nat) (st : List Nat) : List Nat :=
  if h : i < n then
    let x := nums[i]!
    match st with
    | [] => buildStack_aux nums n (i + 1) [i]
    | j :: _ =>
      if x < nums[j]! then
        buildStack_aux nums n (i + 1) (i :: st)
      else
        buildStack_aux nums n (i + 1) st
  else
    st
termination_by n - i
decreasing_by all_goals (simp_wf; grind)

/-
Auxiliary definition for `popWhile` lifted to the top level.
-/
def popWhile_aux (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) : List Nat × Nat :=
  match st with
  | [] => ([], best)
  | i :: rest =>
    if nums[i]! ≤ nums[j]! then
      popWhile_aux nums j rest (Nat.max best (j - i))
    else
      (st, best)

/-
Auxiliary definition for `scanRight` lifted to the top level. Removed `decreasing_by` as termination is structural.
-/
def scanRight_aux (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) (best : Nat) : Nat :=
  if hj : j < n then
    let (st', best') := popWhile_aux nums j st best
    match j with
    | 0 => best'
    | j' + 1 => scanRight_aux nums n j' st' best'
  else
    best
termination_by j

/-
Equivalence between `implementation` and auxiliary functions.
-/
theorem impl_eq_aux (nums : Array Int) :
  nums.size > 1 →
  implementation nums = scanRight_aux nums nums.size (nums.size - 1) (buildStack_aux nums nums.size 0 []) 0 := by
  -- By definition of `implementation`, if `n > 1`, then `implementation nums` is equal to `scanRight_aux nums n (n - 1) (buildStack_aux nums n 0 []) 0`.
  intros h
  simp [implementation, h];
  rw [ if_neg h.not_le ];
  -- By definition of `implementation.buildStack`, we know that it is equivalent to `buildStack_aux`.
  have h_buildStack : ∀ (nums : Array Int) (n : Nat) (i : Nat) (st : List Nat), implementation.buildStack nums n i st = buildStack_aux nums n i st := by
    intros nums n i st
    induction' h : n - i using Nat.strong_induction_on with m ih generalizing i st;
    unfold implementation.buildStack buildStack_aux;
    split_ifs <;> simp_all +decide [ Nat.sub_succ ];
    cases st <;> simp +decide [ * ];
    · exact ih _ ( by omega ) _ _ rfl;
    · grind;
  -- By definition of `implementation.popWhile`, we know that it is equivalent to `popWhile_aux`.
  have h_popWhile : ∀ (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat), implementation.popWhile nums j st best = popWhile_aux nums j st best := by
    intros nums j st best; exact (by
    induction' st with i st ih generalizing j best;
    · -- In the base case, when the stack is empty, both functions return the same result.
      simp [implementation.popWhile, popWhile_aux];
    · unfold implementation.popWhile popWhile_aux; aesop;);
  -- By definition of `implementation.scanRight`, we know that it is equivalent to `scanRight_aux`.
  have h_scanRight : ∀ (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) (best : Nat), implementation.scanRight nums n j st best = scanRight_aux nums n j st best := by
    intros nums n j st best; exact (by
    induction' j with j ih generalizing st best <;> simp_all +decide [ Nat.succ_eq_add_one ];
    · unfold implementation.scanRight scanRight_aux; aesop;
    · unfold implementation.scanRight scanRight_aux; aesop;);
  rw [ h_scanRight, h_buildStack ]

/-
Definition of the invariant: the stack `st` covers all indices `k < i`.
-/
def StackCovers (nums : Array Int) (i : Nat) (st : List Nat) : Prop :=
  ∀ k < i, ∃ s ∈ st, s ≤ k ∧ nums[s]! ≤ nums[k]!

/-
Helper definition: one step of building the stack.
-/
def buildStack_step (nums : Array Int) (i : Nat) (st : List Nat) : List Nat :=
  match st with
  | [] => [i]
  | j :: _ => if nums[i]! < nums[j]! then i :: st else st

/-
Definition of `StackBounded`: all elements in the stack are strictly less than `i`.
-/
def StackBounded (i : Nat) (st : List Nat) : Prop :=
  ∀ s ∈ st, s < i

/-
Lemma: `buildStack_step` preserves the `StackBounded` property (with bound increased by 1).
-/
theorem buildStack_step_bounded (nums : Array Int) (i : Nat) (st : List Nat) :
  StackBounded i st → StackBounded (i + 1) (buildStack_step nums i st) := by
    -- Let's unfold the definition of `buildStack_step`.
    simp [buildStack_step];
    intro h; rcases st with ( _ | ⟨ j, _ | ⟨ k, st ⟩ ⟩ ) <;> simp_all +decide [ StackBounded ] ;
    · grind;
    · grind +ring

/-
Lemma: `buildStack_step` preserves `StackCovers` (extending coverage to `i`), provided `StackBounded` holds.
-/
theorem buildStack_step_covers_with_bound (nums : Array Int) (i : Nat) (st : List Nat) :
  StackCovers nums i st →
  StackBounded i st →
  StackCovers nums (i + 1) (buildStack_step nums i st) := by
    unfold StackCovers StackBounded;
    intro h1 h2 k hk; cases lt_or_eq_of_le ( Nat.le_of_lt_succ hk ) <;> simp_all +decide [ buildStack_step ] ;
    · cases st <;> simp_all +decide [ Nat.lt_succ_iff ];
      · linarith [ h1 k ];
      · grind;
    · cases st <;> simp_all +decide [ lt_irrefl ];
      grind +ring

/-
Equivalence of `buildStack_aux` step to `buildStack_step`.
-/
theorem buildStack_aux_eq_step (nums : Array Int) (n : Nat) (i : Nat) (st : List Nat) :
  buildStack_aux nums n i st =
  if i < n then
    buildStack_aux nums n (i + 1) (buildStack_step nums i st)
  else
    st := by
  conv => lhs; unfold buildStack_aux
  split_ifs
  · simp [buildStack_step]
    cases st
    · simp
    · simp
      split_ifs
      · rfl
      · rfl
  · rfl

/-
Generalized lemma: `buildStack_aux` produces a stack that covers all indices `< n`, given that the input stack covers `< i`.
-/
theorem buildStack_aux_covers (nums : Array Int) (n : Nat) (i : Nat) (st : List Nat) :
  i ≤ n →
  StackCovers nums i st →
  StackBounded i st →
  StackCovers nums n (buildStack_aux nums n i st) := by
    -- By definition of `buildStack_aux`, we know that it builds a stack covering all indices up to `n`.
    intro hn hstack hbounded
    induction' k : n - i with k ih generalizing i st;
    · rw [ Nat.sub_eq_iff_eq_add ] at k;
      · unfold buildStack_aux; aesop;
      · grind;
    · convert ih ( i + 1 ) ( buildStack_step nums i st ) ( by omega ) ( buildStack_step_covers_with_bound nums i st hstack hbounded ) ( buildStack_step_bounded nums i st hbounded ) ( by omega ) using 1;
      rw [ buildStack_aux_eq_step ] ; aesop

/-
Definition of `StackSorted` and preservation lemma.
-/
def StackSorted (nums : Array Int) (st : List Nat) : Prop :=
  List.Chain' (fun a b => nums[a]! < nums[b]!) st

theorem buildStack_step_sorted (nums : Array Int) (i : Nat) (st : List Nat) :
  StackSorted nums st → StackSorted nums (buildStack_step nums i st) := by
    unfold buildStack_step;
    rcases st with ( _ | ⟨ j, st ⟩ ) <;> simp_all +decide [ List.Chain', StackSorted ];
    grind

/-
Lemma: `buildStack_step` preserves descending indices.
-/
def StackIndicesDescending (st : List Nat) : Prop :=
  List.Chain' (fun a b => a > b) st

theorem buildStack_step_indices_descending (nums : Array Int) (i : Nat) (st : List Nat) :
  StackIndicesDescending st →
  StackBounded i st →
  StackIndicesDescending (buildStack_step nums i st) := by
    cases st <;> simp_all +decide [ buildStack_step ];
    · tauto;
    · split_ifs <;> simp_all +decide [ StackBounded, StackIndicesDescending ];
      simp_all +decide [ List.Chain' ]

/-
Lemma: If `popWhile` returns 0, then any popped element `s` must satisfy `s >= j`.
-/
theorem popWhile_zero_implies (nums : Array Int) (j : Nat) (st : List Nat) :
  (popWhile_aux nums j st 0).2 = 0 →
  ∀ s ∈ st, s ∉ (popWhile_aux nums j st 0).1 → s ≥ j := by
  revert st;
  -- By definition of `popWhile_aux`, if it returns `(st', 0)`, then the `best` value is 0, which implies that no element in `st'` is less than or equal to `j`.
  have h_popWhile_zero : ∀ (st : List ℕ) (best : ℕ), (popWhile_aux nums j st best).2 = 0 → best = 0 ∧ ∀ s ∈ st, s∉ (popWhile_aux nums j st best).1 → s ≥ j := by
    intros st best hbest
    induction' st with s st ih generalizing best;
    · unfold popWhile_aux at hbest; aesop;
    · unfold popWhile_aux at hbest ⊢; simp_all +decide ;
      grind +ring;
  exact fun st hst s hs hs' => h_popWhile_zero st 0 hst |>.2 s hs hs'

/-
Lemma: `popWhile` only increases `best`.
-/
theorem popWhile_aux_ge_best (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
  (popWhile_aux nums j st best).2 ≥ best := by
  induction st generalizing best with
  | nil => simp [popWhile_aux]
  | cons i rest ih =>
    unfold popWhile_aux
    split_ifs
    · apply le_trans _ (ih _)
      apply le_max_left
    · simp

/-
Lemma: `popWhile` preserves `StackSorted`.
-/
theorem popWhile_preserves_sorted (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
  StackSorted nums st → StackSorted nums (popWhile_aux nums j st best).1 := by
    intro h_sorted;
    induction' st with i st ih generalizing best;
    · exact?;
    · unfold popWhile_aux;
      split_ifs <;> simp_all +decide [ StackSorted ];
      exact ih _ ( List.chain'_cons'.mp h_sorted |>.2 )

/-
Lemma: `popWhile` returns a subset (sublist) of the input stack.
-/
theorem popWhile_subset (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
  ∀ s ∈ (popWhile_aux nums j st best).1, s ∈ st := by
  induction st generalizing best with
  | nil => simp [popWhile_aux]
  | cons i rest ih =>
    unfold popWhile_aux
    split_ifs
    · intro s hs
      exact List.mem_cons_of_mem _ (ih _ s hs)
    · intro s hs
      exact hs

/-
Lemma: All elements remaining in the stack after `popWhile` have values strictly greater than `nums[j]`.
-/
theorem popWhile_keeps_greater (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
  StackSorted nums st →
  ∀ s ∈ (popWhile_aux nums j st best).1, nums[s]! > nums[j]! := by
    intro h_sorted s hs;
    induction' st with i rest ih generalizing best;
    · cases hs;
    · unfold popWhile_aux at hs;
      split_ifs at hs <;> simp_all +decide [ StackSorted ];
      · exact ih _ ( List.chain'_cons'.mp h_sorted |>.2 ) hs;
      · rcases hs with ( rfl | hs ) <;> [ tauto; exact ih _ ( List.chain'_cons'.1 h_sorted |>.2 ) hs ];
        have := List.isChain_iff_get.mp h_sorted;
        -- By induction on the position of `s` in `rest`, we can show that `nums[i]! < nums[s]!`.
        have h_ind : ∀ k < rest.length, nums[i]! < nums[rest.get! k]! := by
          intro k hk; induction' k with k ih <;> simp_all +decide [ List.get ] ;
          · simpa using this 0 hk;
          · exact lt_trans ( ih ( Nat.lt_of_succ_lt hk ) ) ( this _ hk );
        obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hs;
        simpa [ ← hk ] using lt_trans ‹nums[j]! < nums[i]!› ( h_ind k k.2 )

/-
Lemma: `scanRight` only increases `best`.
-/
theorem scanRight_aux_ge_best (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) (best : Nat) :
  scanRight_aux nums n j st best >= best := by
  induction j generalizing st best with
  | zero =>
    unfold scanRight_aux
    split_ifs
    · generalize h_pop : popWhile_aux nums 0 st best = res
      obtain ⟨st', best'⟩ := res
      have h_ge := popWhile_aux_ge_best nums 0 st best
      rw [h_pop] at h_ge
      simp at h_ge
      simp
      exact h_ge
    · exact Nat.le_refl _
  | succ j ih =>
    unfold scanRight_aux
    split_ifs
    · generalize h_pop : popWhile_aux nums (j + 1) st best = res
      obtain ⟨st', best'⟩ := res
      have h_ge := popWhile_aux_ge_best nums (j + 1) st best
      rw [h_pop] at h_ge
      simp at h_ge
      simp
      apply Nat.le_trans h_ge
      apply ih
    · exact Nat.le_refl _

/-
Lemma: If `scanRight` returns 0, then for all `s` in stack, no ramp starts at `s` ending at any `k <= j`. Assumes `j < n`.
-/
theorem scan_zero_implies (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) :
  j < n →
  StackSorted nums st →
  scanRight_aux nums n j st 0 = 0 →
  (∀ s ∈ st, ∀ k ≤ j, k < n → s < k → nums[s]! > nums[k]!) := by
    intro hj hst hscan s hs k hk₁ hk₂ hk₃;
    induction' j with j ih generalizing st k s;
    · grind;
    · -- If `popWhile_aux` returns 0, then any popped element `s` must satisfy `s >= j+1`.
      by_cases hpop : (popWhile_aux nums (j + 1) st 0).2 = 0;
      · by_cases hk : k = j + 1;
        · have hpop : ∀ s ∈ (popWhile_aux nums (j + 1) st 0).1, nums[s]! > nums[j + 1]! := by
            exact?;
          by_cases hs' : s ∈ (popWhile_aux nums (j + 1) st 0).1 <;> simp_all +decide;
          have := popWhile_zero_implies nums ( j + 1 ) st ‹_› s hs hs'; linarith;
        · apply ih (popWhile_aux nums (j + 1) st 0).1 (by
          linarith) (by
          exact?) (by
          unfold scanRight_aux at hscan; aesop;) s (by
          have hpop : ∀ s ∈ st, s∉ (popWhile_aux nums (j + 1) st 0).1 → s ≥ j + 1 := by
            exact?;
          exact Classical.not_not.1 fun h => by linarith [ hpop s hs h, Nat.lt_of_le_of_ne hk₁ hk ] ;) k (by
          omega) (by
          linarith) hk₃;
      · unfold scanRight_aux at hscan;
        contrapose! hscan;
        simp [hj, hpop];
        exact ne_of_gt ( lt_of_lt_of_le ( Nat.pos_of_ne_zero hpop ) ( scanRight_aux_ge_best _ _ _ _ _ ) )

/-
Lemma: If `scanRight` returns 0, then for all `s` in stack, no ramp starts at `s` ending at any `k <= j`. Assumes `j < n`.
-/
theorem scan_zero_implies_v2 (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) :
  j < n →
  StackSorted nums st →
  scanRight_aux nums n j st 0 = 0 →
  (∀ s ∈ st, ∀ k ≤ j, k < n → s < k → nums[s]! > nums[k]!) := by
    -- Apply the lemma `scan_zero_implies` to conclude the proof.
    apply scan_zero_implies

/-
Lemma: If `scanRight` returns 0, then for all `s` in stack, no ramp starts at `s` ending at any `k <= j`. Assumes `j < n`.
-/
theorem scan_zero_implies_v3 (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) :
  j < n →
  StackSorted nums st →
  scanRight_aux nums n j st 0 = 0 →
  (∀ s ∈ st, ∀ k ≤ j, k < n → s < k → nums[s]! > nums[k]!) := by
    apply scan_zero_implies_v2

/-
Lemma: `buildStack_aux` produces a sorted stack.
-/
theorem buildStack_aux_sorted (nums : Array Int) (n : Nat) (i : Nat) (st : List Nat) :
  i ≤ n →
  StackSorted nums st →
  StackSorted nums (buildStack_aux nums n i st) := by
    intro hi hst;
    -- By induction on `n - i`.
    induction' k : n - i with k ih generalizing i st;
    · unfold buildStack_aux;
      rw [ Nat.sub_eq_iff_eq_add ] at k <;> aesop;
    · convert ih ( i + 1 ) ( buildStack_step nums i st ) ( by omega ) ( buildStack_step_sorted nums i st hst ) ( by omega ) using 1;
      rw [ buildStack_aux_eq_step ] ; aesop

end AristotleLemmas

theorem correctness_goal_0 (nums : Array ℤ) (h_precond : precondition nums) (n : ℕ) (hsmall : n ≤ 1) (himpl : implementation nums = 0) (w : ℕ) (hw : IsRampWidth nums w) : ¬IsRampWidth nums w := by
    obtain ⟨ i, j, h ⟩ := hw;
    rcases h with ⟨ ⟨ hij, hlt, hle ⟩, rfl ⟩;
    -- Apply the contradiction hypothesis to obtain that `scanRight_aux` must be zero.
    have h_scan_zero : scanRight_aux nums nums.size (nums.size - 1) (buildStack_aux nums nums.size 0 []) 0 = 0 := by
      rw [ ← impl_eq_aux nums ( by linarith ), himpl ];
    have h_contradiction : ∀ s ∈ buildStack_aux nums nums.size 0 [], ∀ k ≤ nums.size - 1, k < nums.size → s < k → nums[s]! > nums[k]! := by
      apply scan_zero_implies_v2;
      · omega;
      · apply buildStack_aux_sorted;
        · norm_num;
        · exact List.isChain_nil;
      · exact h_scan_zero;
    -- Apply the cover property to find such an s.
    obtain ⟨ s, hs₁, hs₂ ⟩ : ∃ s ∈ buildStack_aux nums nums.size 0 [], s ≤ i ∧ nums[s]! ≤ nums[i]! := by
      apply (buildStack_aux_covers nums nums.size 0 [] (by linarith) (by
      exact fun k hk => by linarith;) (by
      exact fun s hs => by contradiction;)) i (by linarith);
    linarith [ h_contradiction s hs₁ j ( Nat.le_sub_one_of_lt hlt ) hlt ( by linarith ) ]

noncomputable section AristotleLemmas

/-
Auxiliary function mirroring `buildStack` from the implementation.
-/
def Aux_buildStack (nums : Array Int) (i : Nat) (st : List Nat) : List Nat :=
  if h : i < nums.size then
    let x := nums[i]!
    match st with
    | [] => Aux_buildStack nums (i + 1) [i]
    | j :: _ =>
      if x < nums[j]! then
        Aux_buildStack nums (i + 1) (i :: st)
      else
        Aux_buildStack nums (i + 1) st
  else
    st
termination_by nums.size - i

/-
Auxiliary function mirroring `popWhile` from the implementation.
-/
def Aux_popWhile (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) : List Nat × Nat :=
  match st with
  | [] => ([], best)
  | i :: rest =>
    if nums[i]! ≤ nums[j]! then
      Aux_popWhile nums j rest (Nat.max best (j - i))
    else
      (st, best)
termination_by st.length

/-
Auxiliary function mirroring `scanRight` from the implementation.
-/
def Aux_scanRight (nums : Array Int) (n : Nat) (j : Nat) (st : List Nat) (best : Nat) : Nat :=
  if hj : j < n then
    let (st', best') := Aux_popWhile nums j st best
    match j with
    | 0 => best'
    | j' + 1 => Aux_scanRight nums n j' st' best'
  else
    best
termination_by j

/-
Predicate stating that the stack is sorted by index (decreasing) and value (strictly decreasing).
-/
def StackSorted (nums : Array Int) (st : List Nat) : Prop :=
  List.Sorted (fun a b => a > b ∧ nums[a]! < nums[b]!) st

/-
The implementation is equivalent to the composition of the auxiliary functions.
Note: `Aux_buildStack` takes `nums`, `i`, `st`. The `n` parameter was removed in the successful definition.
The implementation calls `buildStack 0 []`.
The implementation calls `scanRight (n - 1) st 0`.
The condition `n <= 1` is handled by the `if`.
-/
theorem implementation_eq_aux (nums : Array Int) :
  implementation nums =
    if h : nums.size ≤ 1 then 0
    else Aux_scanRight nums nums.size (nums.size - 1) (Aux_buildStack nums 0 []) 0 := by
  -- By definition of `Aux_buildStack` and `Aux_scanRight`, they are equivalent to the corresponding functions in the implementation.
  have h_equiv : ∀ (i : Nat) (st : List Nat), Aux_buildStack nums i st = implementation.buildStack nums nums.size i st := by
    intro i st; induction' n : nums.size - i using Nat.strong_induction_on with n ih generalizing i st;
    unfold Aux_buildStack implementation.buildStack;
    split_ifs <;> simp_all +decide;
    cases st <;> simp +decide [ * ];
    · exact ih _ ( by omega ) _ _ rfl;
    · split_ifs <;> [ exact ih _ ( by omega ) _ _ rfl; exact ih _ ( by omega ) _ _ rfl ];
  -- By definition of `Aux_popWhile` and `Aux_scanRight`, they are equivalent to the corresponding functions in the implementation.
  have h_equiv_pop : ∀ (j : Nat) (st : List Nat) (best : Nat), Aux_popWhile nums j st best = implementation.popWhile nums j st best := by
    intros j st best;
    induction' st with i st ih generalizing j best;
    · -- In the base case, when the stack is empty, both `Aux_popWhile` and `implementation.popWhile` return `([], best)`.
      simp [Aux_popWhile, implementation.popWhile];
    · unfold Aux_popWhile implementation.popWhile; aesop;
  have h_equiv_scan : ∀ (j : Nat) (st : List Nat) (best : Nat), Aux_scanRight nums nums.size j st best = implementation.scanRight nums nums.size j st best := by
    intros j st best
    induction' j with j ih generalizing st best;
    · unfold Aux_scanRight implementation.scanRight; aesop;
    · unfold Aux_scanRight implementation.scanRight; aesop;
  aesop

/-
Definition of the stack covering invariant and a lemma stating that `Aux_buildStack` only adds elements to the stack (so the initial stack is a subset of the final stack).
-/
def StackCoversPrefix (nums : Array Int) (limit : Nat) (st : List Nat) : Prop :=
  ∀ x < limit, ∃ k ∈ st, k ≤ x ∧ nums[k]! ≤ nums[x]!

theorem buildStack_subset (nums : Array Int) (i : Nat) (st : List Nat) :
  st ⊆ Aux_buildStack nums i st := by
  induction' n : nums.size - i using Nat.strong_induction_on with n ih generalizing i st;
  unfold Aux_buildStack;
  cases st <;> simp_all +decide [ List.subset_def ];
  grind

/-
Invariant for the stack building process:
1. The stack covers all indices `x < i`.
2. All indices in the stack are strictly less than `i`.
-/
def StackInvariant (nums : Array Int) (i : Nat) (st : List Nat) : Prop :=
  StackCoversPrefix nums i st ∧ ∀ k ∈ st, k < i

/-
Base case for the stack invariant: initially (at index 0 with empty stack), the invariant holds vacuously.
-/
theorem StackInvariant_initial (nums : Array Int) :
  StackInvariant nums 0 [] := by
  -- The base case is when `i = 0`. In this case, the stack is empty, so `StackCoversPrefix` holds trivially because there are no `x` less than `0` to check.
  simp [StackInvariant, StackCoversPrefix]

/-
Inductive step for the stack invariant when pushing `i` onto the stack.
If the invariant holds for `i` and `st`, then it holds for `i + 1` and `i :: st`.
Proof sketch:
1. Coverage: For `x < i + 1`:
   - If `x = i`, `k = i` (which is in `i :: st`) covers it.
   - If `x < i`, the old stack `st` covered it, and `st` is a subset of `i :: st`.
2. Bound: Elements in `i :: st` are either `i` (which is `< i + 1`) or in `st` (which are `< i < i + 1`).
-/
theorem StackInvariant_step_push (nums : Array Int) (i : Nat) (st : List Nat)
    (h : StackInvariant nums i st) :
    StackInvariant nums (i + 1) (i :: st) := by
  unfold StackInvariant at *;
  unfold StackCoversPrefix at *;
  grind +ring

/-
Inductive step for the stack invariant when skipping `i`.
If the invariant holds for `i` and `st`, and `nums[top] <= nums[i]`, then it holds for `i + 1` and `st`.
Proof sketch:
1. Coverage: For `x < i + 1`:
   - If `x < i`, covered by `st` (from `h_inv`).
   - If `x = i`: `j` is in `st` (it's the head), `j < i` (from `h_inv`), and `nums[j] <= nums[i]`. So `j` covers `i`.
2. Bound: Elements in `st` are `< i`, so they are `< i + 1`.
-/
theorem StackInvariant_step_skip (nums : Array Int) (i : Nat) (j : Nat) (tail : List Nat) (st : List Nat)
    (h_st : j :: tail = st)
    (h_inv : StackInvariant nums i st)
    (h_val : nums[j]! ≤ nums[i]!) :
    StackInvariant nums (i + 1) st := by
  apply And.intro;
  · intro x hx
    by_cases hx_lt : x < i;
    · exact h_inv.1 x hx_lt;
    · rw [ show x = i by linarith ];
      exact ⟨ j, by aesop, by linarith [ h_inv.2 j ( by aesop ) ], h_val ⟩;
  · exact fun k hk => Nat.lt_succ_of_lt ( h_inv.2 k hk )

/-
Unfolding lemma for `Aux_buildStack`.
-/
theorem Aux_buildStack_eq (nums : Array Int) (i : Nat) (st : List Nat) :
    Aux_buildStack nums i st =
    if h : i < nums.size then
      let x := nums[i]!
      match st with
      | [] => Aux_buildStack nums (i + 1) [i]
      | j :: _ =>
        if x < nums[j]! then
          Aux_buildStack nums (i + 1) (i :: st)
        else
          Aux_buildStack nums (i + 1) st
    else
      st := by
        exact?

/-
The stack invariant holds for the final stack produced by `Aux_buildStack`.
We prove this by strong induction on `nums.size - i`.
If `i < nums.size`, we step to `i + 1`.
- If we push `i`, we use `StackInvariant_step_push`.
- If we skip `i` (pop `j`), we use `StackInvariant_step_skip`.
If `i = nums.size`, we are done.
-/
theorem StackInvariant_final (nums : Array Int) (i : Nat) (st : List Nat)
    (h_inv : StackInvariant nums i st) (hi : i ≤ nums.size) :
    StackInvariant nums nums.size (Aux_buildStack nums i st) := by
      -- By induction on $j = \text{nums.size} - i$, we can show that the stack invariant holds at each step.
      induction' j : nums.size - i with j ih generalizing i st;
      · rw [ Nat.sub_eq_iff_eq_add hi ] at j;
        unfold Aux_buildStack; aesop;
      · -- By definition of `Aux_buildStack`, we know that if `i < nums.size`, then we can step to `i + 1`.
        by_cases hpush : i < nums.size;
        · rw [Aux_buildStack_eq];
          cases st <;> simp_all +decide [ StackInvariant_step_push, StackInvariant_step_skip ];
          · convert ih ( i + 1 ) [ i ] _ _ _ using 1;
            · exact?;
            · linarith;
            · omega;
          · split_ifs <;> [ exact ih _ _ ( StackInvariant_step_push _ _ _ h_inv ) ( by omega ) ( by omega ) ; exact ih _ _ ( StackInvariant_step_skip _ _ _ _ _ rfl h_inv ( by
              grind ) ) ( by omega ) ( by omega ) ];
        · omega

/-
The stack invariant holds for the final stack produced by `Aux_buildStack`.
We prove this by strong induction on `nums.size - i`.
If `i < nums.size`, we step to `i + 1`.
- If we push `i`, we use `StackInvariant_step_push`.
- If we skip `i` (pop `j`), we use `StackInvariant_step_skip`.
If `i = nums.size`, we are done.
-/
theorem StackInvariant_final_proof (nums : Array Int) (i : Nat) (st : List Nat)
    (h_inv : StackInvariant nums i st) (hi : i ≤ nums.size) :
    StackInvariant nums nums.size (Aux_buildStack nums i st) := by
      exact?

/-
The stack invariant holds for the final stack produced by `Aux_buildStack`.
We prove this by strong induction on `nums.size - i`.
If `i < nums.size`, we step to `i + 1`.
- If we push `i`, we use `StackInvariant_step_push`.
- If we skip `i` (pop `j`), we use `StackInvariant_step_skip`.
If `i = nums.size`, we are done.
-/
theorem StackInvariant_final_v2 (nums : Array Int) (i : Nat) (st : List Nat)
    (h_inv : StackInvariant nums i st) (hi : i ≤ nums.size) :
    StackInvariant nums nums.size (Aux_buildStack nums i st) := by
  induction' k : nums.size - i using Nat.strong_induction_on with k ih generalizing i st
  rw [Aux_buildStack_eq]
  split_ifs with h_lt
  · -- Case i < nums.size
    match h_st : st with
    | [] =>
      -- st = []
      simp only [h_st]
      apply ih (nums.size - (i + 1))
      · omega
      · exact StackInvariant_step_push nums i [] h_inv
      · exact h_lt
      · rfl
    | j :: tail =>
      -- st = j :: tail
      simp only [h_st]
      -- We need to expose the if.
      -- The term is `if nums[i]! < nums[j]! then ... else ...`
      by_cases h_val : nums[i]! < nums[j]!
      · rw [if_pos h_val]
        apply ih (nums.size - (i + 1))
        · omega
        · exact StackInvariant_step_push nums i (j :: tail) h_inv
        · exact h_lt
        · rfl
      · rw [if_neg h_val]
        apply ih (nums.size - (i + 1))
        · omega
        · apply StackInvariant_step_skip nums i j tail (j :: tail) rfl h_inv
          push_neg at h_val
          exact h_val
        · exact h_lt
        · rfl
  · -- Case i >= nums.size
    have : i = nums.size := by omega
    subst this
    exact h_inv

/-
The stack invariant holds for the final stack produced by `Aux_buildStack`.
We prove this by strong induction on `nums.size - i`.
If `i < nums.size`, we step to `i + 1`.
- If we push `i`, we use `StackInvariant_step_push`.
- If we skip `i` (pop `j`), we use `StackInvariant_step_skip`.
If `i = nums.size`, we are done.
-/
theorem StackInvariant_final_v3 (nums : Array Int) (i : Nat) (st : List Nat)
    (h_inv : StackInvariant nums i st) (hi : i ≤ nums.size) :
    StackInvariant nums nums.size (Aux_buildStack nums i st) := by
      -- Apply the induction hypothesis to conclude the proof.
      apply StackInvariant_final_v2 nums i st h_inv hi

/-
The stack produced by `Aux_buildStack` is sorted (indices decreasing, values strictly decreasing).
Proof by induction on `nums.size - i`.
Base case: `i = nums.size`, returns `st`. If `st` is sorted, we are good.
Step:
- Push `i`: `i` is pushed only if `nums[i] < nums[top]`.
  Since `top < i` (indices increase as we go), `i > top`.
  So `i` is the new top. `i > old_top` and `nums[i] < nums[old_top]`.
  So `i :: st` is sorted.
- Skip `i`: `st` remains sorted.
We need to carry the invariant that `st` is sorted and `∀ k ∈ st, k < i`.
We already have `StackInvariant` which gives `∀ k ∈ st, k < i`.
We just need to add `StackSorted` to the invariant.
-/
theorem buildStack_sorted (nums : Array Int) :
  StackSorted nums (Aux_buildStack nums 0 []) := by
  -- By induction on `nums.size - i`, we can show that the stack is sorted.
  have h_ind : ∀ i st, StackInvariant nums i st → StackSorted nums st → StackSorted nums (Aux_buildStack nums i st) := by
    intros i st h_inv h_sorted
    induction' n : nums.size - i using Nat.strong_induction_on with n ih generalizing i st;
    by_cases hi : i < nums.size;
    · unfold Aux_buildStack;
      rcases st with ( _ | ⟨ j, tail ⟩ ) <;> simp_all +decide;
      · convert ih _ _ _ _ _ _ rfl using 1;
        · omega;
        · exact?;
        · exact List.sorted_singleton _;
      · split_ifs;
        · convert ih _ _ _ _ _ _ rfl using 1;
          · omega;
          · exact?;
          · unfold StackSorted at *;
            simp_all +decide [ List.Sorted ];
            exact ⟨ h_inv.2 _ ( by aesop ), fun a ha => ⟨ by linarith [ h_inv.2 _ ( by aesop : a ∈ j :: tail ), h_sorted.1 _ ha ], by linarith [ h_sorted.1 _ ha ] ⟩ ⟩;
        · apply ih (nums.size - (i + 1));
          · omega;
          · apply StackInvariant_step_skip;
            exact?;
            · assumption;
            · grind;
          · assumption;
          · rfl;
    · -- Since `i` is not less than the size of the array, the function `Aux_buildStack` returns the stack as is.
      have h_eq : Aux_buildStack nums i st = st := by
        unfold Aux_buildStack; aesop;
      exact h_eq.symm ▸ h_sorted;
  apply h_ind 0 [] (StackInvariant_initial nums) (by
  exact List.sorted_nil)

/-
Specification of `popWhile`:
1. The new stack is a subset (suffix) of the old stack.
2. Popped elements satisfy `nums[i] <= nums[j]`.
3. Remaining elements satisfy `nums[i] > nums[j]`.
4. `best'` is updated correctly.
5. The new stack is still sorted.
-/
theorem popWhile_spec (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat)
    (h_sorted : StackSorted nums st) :
    let (st', best') := Aux_popWhile nums j st best
    (st' ⊆ st) ∧
    (∀ i ∈ st, i ∉ st' → nums[i]! ≤ nums[j]!) ∧
    (∀ i ∈ st', nums[i]! > nums[j]!) ∧
    (best' = best ∨ ∃ i ∈ st, i ∉ st' ∧ best' = Nat.max best (j - i)) ∧
    (StackSorted nums st') := by
  induction' st with i st ih generalizing best;
  · unfold Aux_popWhile; aesop;
  · unfold Aux_popWhile;
    split_ifs <;> simp_all +decide [ List.subset_def ];
    · specialize ih ( best.max ( j - i ) ) ( by
        exact h_sorted.tail );
      grind;
    · intro a ha; have := h_sorted; simp_all +decide [ StackSorted ] ;
      linarith [ h_sorted.1 a ha ]

/-
Invariant for the scan loop.
`j` is an integer because it can go down to -1 (conceptually).
Actually, `Aux_scanRight` uses `Nat` `j`.
But the invariant talks about `v > j`.
If `j = n - 1`, `v > j` means `v >= n`, which is impossible for valid indices.
So the conditions are vacuously true initially.
`StackSorted` holds by `buildStack_sorted`.
So `ScanInvariant_initial` should be easy.
-/
def ScanInvariant (nums : Array Int) (j : Int) (st : List Nat) (best : Nat) : Prop :=
  StackSorted nums st ∧
  (∀ u ∈ st, ∀ v : Nat, j < v → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ u v : Nat, j < v → v < nums.size → IsRamp nums u v → v - u ≤ best)

theorem ScanInvariant_initial (nums : Array Int) :
  ScanInvariant nums (nums.size - 1) (Aux_buildStack nums 0 []) 0 := by
  constructor;
  · exact?;
  · grind +ring

/-
Stronger invariant `ScanInvariant2`.
1. `StackSorted`.
2. `st ⊆ st0`.
3. Remaining elements in `st` are strictly greater than all processed elements `v > j`.
4. Popped elements `k ∈ st0 \ st` have been "witnessed" by some `v > j` where `IsRamp k v` and `v - k ≤ best`.
5. Global correctness for processed elements: any ramp ending at `v > j` has width `≤ best`.

Initial state `j = n - 1`:
- `v > n - 1` is impossible.
- Clauses 3, 4, 5 are vacuously true.
- `st = st0` so `st ⊆ st0` and `k ∉ st` is false.
- `StackSorted` holds.
-/
def ScanInvariant2 (nums : Array Int) (st0 : List Nat) (j : Int) (st : List Nat) (best : Nat) : Prop :=
  StackSorted nums st ∧
  st ⊆ st0 ∧
  (∀ u ∈ st, ∀ v : Nat, j < v → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ k ∈ st0, k ∉ st → ∃ v : Nat, j < v ∧ v < nums.size ∧ IsRamp nums k v ∧ v - k ≤ best) ∧
  (∀ u v : Nat, j < v → v < nums.size → IsRamp nums u v → v - u ≤ best)

theorem ScanInvariant2_initial (nums : Array Int) :
  let st0 := Aux_buildStack nums 0 []
  ScanInvariant2 nums st0 (nums.size - 1) st0 0 := by
  constructor;
  · exact?;
  · grind

/-
Invariant for the scan loop.
1. `StackSorted`: The stack is sorted.
2. `st ⊆ st0`: The current stack is a subset of the initial stack.
3. `∀ u ∈ st, ∀ v > j`: Remaining elements in the stack are strictly greater than any processed element `v`.
4. `∀ k ∈ st0, ∀ v > j`: If `k` forms a ramp with a processed element `v`, then `v - k ≤ best`.
Initial state: `j = n - 1`.
- `v > n - 1` is impossible for valid indices.
- Clauses 3 and 4 are vacuously true.
- 1 and 2 are true.
-/
def ScanInvariant3 (nums : Array Int) (st0 : List Nat) (j : Int) (st : List Nat) (best : Nat) : Prop :=
  StackSorted nums st ∧
  st ⊆ st0 ∧
  (∀ u ∈ st, ∀ v : Nat, j < v → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ k ∈ st0, ∀ v : Nat, j < v → v < nums.size → IsRamp nums k v → v - k ≤ best)

theorem ScanInvariant3_initial (nums : Array Int) :
  let st0 := Aux_buildStack nums 0 []
  ScanInvariant3 nums st0 (nums.size - 1) st0 0 := by
  apply And.intro;
  · exact?;
  · grind

/-
Definition of `ScanInvariant4` and its initial condition.
1. `StackSorted`.
2. `st ⊆ st0`.
3. `best` is a valid ramp width (or 0).
4. Remaining stack elements are strictly greater than processed elements.
5. Popped elements have a witness ramp covered by `best`.
6. All ramps starting in `st0` and ending in processed elements are covered by `best`.

Initial state `j = n - 1`:
- `v > n - 1` is impossible.
- Clauses 4, 5, 6 are vacuously true.
- `best = 0` satisfies clause 3.
- `st = st0` satisfies 2.
- `StackSorted` holds.
-/
def ScanInvariant4 (nums : Array Int) (st0 : List Nat) (j : Int) (st : List Nat) (best : Nat) : Prop :=
  StackSorted nums st ∧
  st ⊆ st0 ∧
  (best = 0 ∨ IsRampWidth nums best) ∧
  (∀ u ∈ st, ∀ v : Nat, j < v → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ k ∈ st0, k ∉ st → ∃ v : Nat, j < v ∧ v < nums.size ∧ IsRamp nums k v ∧ v - k ≤ best) ∧
  (∀ k ∈ st0, ∀ v : Nat, j < v → v < nums.size → IsRamp nums k v → v - k ≤ best)

theorem ScanInvariant4_initial (nums : Array Int) :
  let st0 := Aux_buildStack nums 0 []
  ScanInvariant4 nums st0 (nums.size - 1) st0 0 := by
  convert ScanInvariant3_initial nums;
  unfold ScanInvariant4 ScanInvariant3; aesop;

/-
Definition of `ScanInvariant6` and its initialization.
This invariant drops the problematic "witness" clause and relies on the global correctness clause.
It also includes the validity of `best`.
-/
def ScanInvariant6 (nums : Array Int) (st0 : List Nat) (j : Int) (st : List Nat) (best : Nat) : Prop :=
  StackSorted nums st ∧
  st ⊆ st0 ∧
  (best = 0 ∨ IsRampWidth nums best) ∧
  (∀ u ∈ st, ∀ v : Nat, j < v → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ k ∈ st0, ∀ v : Nat, j < v → v < nums.size → IsRamp nums k v → v - k ≤ best)

theorem ScanInvariant6_initial (nums : Array Int) :
  let st0 := Aux_buildStack nums 0 []
  ScanInvariant6 nums st0 (nums.size - 1) st0 0 := by
  constructor
  · exact buildStack_sorted nums
  · constructor
    · exact List.Subset.refl _
    · constructor
      · left; rfl
      · constructor
        · intros u hu v hv1 hv2
          -- v > n - 1 and v < n. Impossible.
          omega
        · intros k hk v hv1 hv2 hramp
          omega

/-
Lemma stating that `popWhile` returns a `best'` that is at least `best`, and at least `j - i` for any popped `i`.
-/
theorem popWhile_best_ge (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
    let res := Aux_popWhile nums j st best
    best ≤ res.2 ∧ ∀ i ∈ st, i ∉ res.1 → j - i ≤ res.2 := by
      induction' st with i st ih generalizing best;
      · unfold Aux_popWhile; aesop;
      · unfold Aux_popWhile;
        grind

/-
Lemma stating that `popWhile` returns a `best'` that is at least `best`, and at least `j - i` for any popped `i`. Renamed to v2 to avoid conflicts.
-/
theorem popWhile_best_ge_v2 (nums : Array Int) (j : Nat) (st : List Nat) (best : Nat) :
    let res := Aux_popWhile nums j st best
    best ≤ res.2 ∧ ∀ i ∈ st, i ∉ res.1 → j - i ≤ res.2 := by
      apply popWhile_best_ge

/-
Definition of `ScanInvariant7` and its initialization.
This invariant includes a witness clause `nums[k] <= nums[v]` instead of `IsRamp k v` to handle the `k=j` case.
-/
def ScanInvariant7 (nums : Array Int) (st0 : List Nat) (j : Int) (st : List Nat) (best : Nat) : Prop :=
  StackSorted nums st ∧
  st ⊆ st0 ∧
  (best = 0 ∨ IsRampWidth nums best) ∧
  (∀ u ∈ st, ∀ v : Nat, j < v → v < nums.size → nums[u]! > nums[v]!) ∧
  (∀ k ∈ st0, k ∉ st → ∃ v : Nat, j < v ∧ v < nums.size ∧ nums[k]! ≤ nums[v]! ∧ v - k ≤ best) ∧
  (∀ k ∈ st0, ∀ v : Nat, j < v → v < nums.size → IsRamp nums k v → v - k ≤ best)

theorem ScanInvariant7_initial (nums : Array Int) :
  let st0 := Aux_buildStack nums 0 []
  ScanInvariant7 nums st0 (nums.size - 1) st0 0 := by
  constructor
  · exact buildStack_sorted nums
  · constructor
    · exact List.Subset.refl _
    · constructor
      · left; rfl
      · constructor
        · intros u hu v hv1 hv2
          omega
        · constructor
          · intros k hk_st0 hk_notin
            contradiction
          · intros k hk v hv1 hv2 hramp
            omega

/-
Proof of the inductive step for `ScanInvariant7`.
This time I carefully handled the coercions and the logic for `best'` validity and the witness clause.
The proof uses `popWhile_spec` and `popWhile_best_ge_v2`.
It splits cases on `v = j` vs `v > j` and `k ∈ st` vs `k ∉ st`.
It also handles the `best' > 0` implication for `IsRampWidth`.
-/
theorem ScanInvariant7_step (nums : Array Int) (st0 : List Nat) (j : Nat) (st : List Nat) (best : Nat)
    (h_inv : ScanInvariant7 nums st0 j st best)
    (hj : j < nums.size) :
    let (st', best') := Aux_popWhile nums j st best
    ScanInvariant7 nums st0 (j - 1) st' best' := by
      obtain ⟨hst_sub, hst_valid, hbest_valid, hst_cond, hst_cond_2⟩ := h_inv;
      refine' ⟨ _, _, _, _, _ ⟩;
      · exact popWhile_spec nums j st best hst_sub |>.2.2.2.2;
      · intro k hk; have := popWhile_spec nums j st best hst_sub; aesop;
      · have := popWhile_spec nums j st best hst_sub;
        rcases this.2.2.2.1 with h | ⟨ i, hi, hi', h ⟩ <;> simp_all +decide [ IsRampWidth ];
        cases hbest_valid <;> simp_all +decide [ IsRamp ];
        · contrapose! hst_cond_2;
          grind;
        · cases max_cases best ( j - i ) <;> simp_all +decide [ Nat.sub_eq_zero_of_le ];
          exact Or.inr ⟨ i, j, ⟨ by
            grind, by
            grind, by
            grind ⟩, rfl ⟩;
      · intro u hu v hv₁ hv₂; have := popWhile_spec nums j st best hst_sub; simp_all +decide ;
        grind;
      · have := popWhile_spec nums j st best hst_sub;
        refine' ⟨ _, _ ⟩;
        · intro k hk hk';
          by_cases hk'' : k ∈ st;
          · use j;
            exact ⟨ by linarith, hj, this.2.1 k hk'' hk', by have := popWhile_best_ge_v2 nums j st best; aesop ⟩;
          · obtain ⟨ v, hv₁, hv₂, hv₃, hv₄ ⟩ := hst_cond_2.1 k hk hk'';
            exact ⟨ v, by linarith, hv₂, hv₃, hv₄.trans ( by cases this.2.2.2.1 <;> aesop ) ⟩;
        · intro k hk v hv₁ hv₂ hv₃;
          by_cases hv₄ : v = j;
          · by_cases hk_st : k ∈ st;
            · by_cases hk_st' : k ∈ (Aux_popWhile nums j st best).1;
              · have := this.2.2.1 k hk_st'; simp_all +decide [ IsRamp ] ;
                linarith [ this.2.2.1 k hk_st' ];
              · have := popWhile_best_ge_v2 nums j st best;
                grind;
            · obtain ⟨ v, hv₁, hv₂, hv₃, hv₄ ⟩ := hst_cond_2.1 k hk hk_st;
              have := popWhile_best_ge_v2 nums j st best;
              grind;
          · exact le_trans ( hst_cond_2.2 k hk v ( by omega ) hv₂ hv₃ ) ( by cases this.2.2.2.1 <;> aesop )

/-
Proof of the inductive step for `ScanInvariant7`.
Renamed to `ScanInvariant7_step_v2` to avoid name collision.
Used `Nat.cast_le` and `Nat.cast_lt` for coercions.
The proof logic remains the same.
-/
theorem ScanInvariant7_step_v2 (nums : Array Int) (st0 : List Nat) (j : Nat) (st : List Nat) (best : Nat)
    (h_inv : ScanInvariant7 nums st0 j st best)
    (hj : j < nums.size) :
    let (st', best') := Aux_popWhile nums j st best
    ScanInvariant7 nums st0 ((j : Int) - 1) st' best' := by
      apply_rules [ ScanInvariant7_step ]

/-
Proof of the inductive step for `ScanInvariant7`.
Using `linarith` for coercions and avoiding `subst`.
This should resolve the issues.
-/
theorem ScanInvariant7_step_v3 (nums : Array Int) (st0 : List Nat) (j : Nat) (st : List Nat) (best : Nat)
    (h_inv : ScanInvariant7 nums st0 j st best)
    (hj : j < nums.size) :
    let (st', best') := Aux_popWhile nums j st best
    ScanInvariant7 nums st0 ((j : Int) - 1) st' best' := by
      convert ScanInvariant7_step_v2 nums st0 j st best h_inv hj using 1

/-
Theorem stating that `Aux_scanRight` produces a result that satisfies `ScanInvariant7` at `j = -1`.
Proof by strong induction on `j`.
If `j = 0`, `Aux_scanRight` returns `best'` from `popWhile`. `ScanInvariant7_step_v3` gives the invariant at `-1`.
If `j = j' + 1`, `Aux_scanRight` recurses. `ScanInvariant7_step_v3` gives the invariant at `j'`, which is the hypothesis for the recursive call.
We use `ScanInvariant7_step_v3` which we just proved.
-/
theorem scanRight_invariant_final (nums : Array Int) (st0 : List Nat) (j : Nat) (st : List Nat) (best : Nat)
    (h_inv : ScanInvariant7 nums st0 j st best)
    (hj : j < nums.size) :
    ∃ st_final, ScanInvariant7 nums st0 (-1) st_final (Aux_scanRight nums nums.size j st best) := by
      induction' j with j ih generalizing st best;
      · -- In the base case, when j = 0, the function returns best.
        use (Aux_popWhile nums 0 st best).fst;
        convert ScanInvariant7_step_v3 nums st0 0 st best h_inv hj using 1;
        unfold Aux_scanRight; aesop;
      · -- Apply the ScanInvariant7_step_v3 lemma to get the invariant at j.
        have h_step : ScanInvariant7 nums st0 (j : ℤ) (Aux_popWhile nums (j + 1) st best).1 (Aux_popWhile nums (j + 1) st best).2 := by
          convert ScanInvariant7_step_v3 nums st0 ( j + 1 ) st best h_inv ( by linarith ) using 1;
          norm_num;
        specialize ih (Aux_popWhile nums (j + 1) st best).1 (Aux_popWhile nums (j + 1) st best).2 h_step (by linarith);
        unfold Aux_scanRight; aesop;

/-
Lemma: If the invariant holds at the end (-1) and the initial stack covers all indices, then the result is the maximum ramp width.
Proof:
1. Take any ramp `(i, j)` with width `w = j - i`.
2. Since `st0` covers `i`, there is `k ∈ st0` with `k ≤ i` and `nums[k] ≤ nums[i]`.
3. `nums[k] ≤ nums[i] ≤ nums[j]`, so `(k, j)` is also a ramp.
4. The invariant guarantees `j - k ≤ result`.
5. Since `k ≤ i`, `j - i ≤ j - k`.
6. Thus `w ≤ result`.
-/
theorem result_is_max (nums : Array Int) (st0 : List Nat) (st_final : List Nat) (result : Nat)
    (h_inv : ScanInvariant7 nums st0 (-1) st_final result)
    (h_cover : StackCoversPrefix nums nums.size st0) :
    ∀ w, IsRampWidth nums w → w ≤ result := by
      intros w hw
      obtain ⟨i, j, hij⟩ := hw
      have h_ramp : IsRamp nums i j := by
        exact hij.1
      have h_width : j - i = w := by
        exact hij.2.symm ▸ rfl
      have h_cover : ∃ k ∈ st0, k ≤ i ∧ nums[k]! ≤ nums[i]! := by
        exact h_cover i ( by linarith [ h_ramp.1, h_ramp.2.1 ] ) |> fun ⟨ k, hk₁, hk₂, hk₃ ⟩ => ⟨ k, hk₁, hk₂, hk₃ ⟩ ;
      obtain ⟨k, hk⟩ := h_cover
      have h_ramp_k : IsRamp nums k j := by
        exact ⟨ lt_of_le_of_lt hk.2.1 h_ramp.1, h_ramp.2.1, le_trans hk.2.2 h_ramp.2.2 ⟩
      have h_width_k : j - k ≤ result := by
        exact h_inv.2.2.2.2.2 k hk.1 j ( by linarith ) ( by linarith [ h_ramp.2 ] ) h_ramp_k |> fun h => by linarith;
      have h_width_i : j - i ≤ j - k := by
        exact Nat.sub_le_sub_left hk.2.1 _
      linarith [h_width_i, h_width_k]

end AristotleLemmas

theorem correctness_goal_2_0 (nums : Array ℤ) (h_precond : precondition nums) (n : ℕ) (hsmall : ¬n ≤ 1) (himpl : implementation nums = implementation.scanRight nums n (n - 1) (implementation.buildStack nums n 0 []) 0) (w : ℕ) (hw : IsRampWidth nums w) (hs : ¬nums.size ≤ 1) : ∀ (w : ℕ),
  IsRampWidth nums w →
    w ≤ implementation.scanRight nums nums.size (nums.size - 1) (implementation.buildStack nums nums.size 0 []) 0 := by
    have h_max : ∃ st_final, ScanInvariant7 nums (Aux_buildStack nums 0 []) (-1) st_final (Aux_scanRight nums nums.size (nums.size - 1) (Aux_buildStack nums 0 []) 0) := by
      apply scanRight_invariant_final;
      · convert ScanInvariant7_initial nums using 1;
        rw [ Nat.cast_pred ( by linarith ) ];
      · omega;
    obtain ⟨st_final, h_final⟩ := h_max;
    convert result_is_max nums ( Aux_buildStack nums 0 [] ) st_final ( Aux_scanRight nums nums.size ( nums.size - 1 ) ( Aux_buildStack nums 0 [] ) 0 ) h_final _ using 1;
    · congr! 2;
      congr! 2;
      · ext;
        rename_i nums n j st best;
        induction' j with j ih generalizing st best;
        · -- By definition of `scanRight`, when `j = 0`, it returns `best`.
          simp [implementation.scanRight, Aux_scanRight];
          congr! 2;
          induction' st with i st ih generalizing best <;> simp +decide [ *, implementation.popWhile ];
          · -- By definition of `Aux_popWhile`, when the list is empty, it returns `([], best)`.
            simp [Aux_popWhile];
          · rw [ show Aux_popWhile nums 0 ( i :: st ) best = if nums[i]! ≤ nums[0]! then Aux_popWhile nums 0 st ( Nat.max best ( 0 - i ) ) else ( i :: st, best ) from ?_ ];
            · norm_num;
            · rw [Aux_popWhile];
        · unfold Aux_scanRight;
          unfold implementation.scanRight;
          induction' st with i st ih generalizing best;
          · unfold implementation.popWhile Aux_popWhile; aesop;
          · unfold implementation.popWhile Aux_popWhile; aesop;
      · funext i st; exact (by
        induction' n : nums.size - i using Nat.strong_induction_on with n ih generalizing i st;
        unfold Aux_buildStack;
        split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
        · rw [ implementation.buildStack ];
          cases st <;> simp +decide [ * ];
          · exact ih _ ( by omega ) _ _ rfl;
          · grind +ring;
        · unfold implementation.buildStack; aesop;);
    · have h_cover : StackInvariant nums nums.size (Aux_buildStack nums 0 []) := by
        apply StackInvariant_final_v3 nums 0 [] (StackInvariant_initial nums) (by linarith);
      exact h_cover.1

end Proof