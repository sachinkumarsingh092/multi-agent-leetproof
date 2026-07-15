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

section Assertions
-- Test case 1
#assert_same_evaluation #[(implementation test1_nums), test1_Expected]

-- Test case 2
#assert_same_evaluation #[(implementation test2_nums), test2_Expected]

-- Test case 3
#assert_same_evaluation #[(implementation test3_nums), test3_Expected]

-- Test case 4
#assert_same_evaluation #[(implementation test4_nums), test4_Expected]

-- Test case 5
#assert_same_evaluation #[(implementation test5_nums), test5_Expected]

-- Test case 6
#assert_same_evaluation #[(implementation test6_nums), test6_Expected]

-- Test case 7
#assert_same_evaluation #[(implementation test7_nums), test7_Expected]

-- Test case 8
#assert_same_evaluation #[(implementation test8_nums), test8_Expected]

-- Test case 9
#assert_same_evaluation #[(implementation test9_nums), test9_Expected]
end Assertions

section Pbt
method implementationPbt (nums : Array Nat)
  return (result : Array Nat)
  require precondition nums
  ensures postcondition nums result
  do
  return (implementation nums)

velvet_plausible_test implementationPbt (config := { maxMs := some 20000 })
end Pbt

section Proof
theorem correctness_goal_0
    (nums : Array ℕ)
    (counts : ℕ × ℕ × ℕ)
    (hcounts : counts =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 => if x = 0 then (c0 + 1, c1, c2) else if x = 1 then (c0, c1 + 1, c2) else (c0, c1, c2 + 1)) fst
            fst_1 snd)
    (0, 0, 0) nums)
    (c0 : ℕ)
    (c1 : ℕ)
    (c2 : ℕ)
    (hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2))
    : c0 = Array.count 0 nums := by
  have hc0 : counts.1 = c0 := by
    simpa using congrArg (fun t => t.1) hproj

  let stepTriple : (Nat × Nat × Nat) → Nat → (Nat × Nat × Nat) :=
    fun acc x =>
      Prod.casesOn acc (fun fst snd =>
        Prod.casesOn snd (fun fst_1 snd =>
          (fun c0 c1 c2 =>
              if x = 0 then (c0 + 1, c1, c2)
              else if x = 1 then (c0, c1 + 1, c2)
              else (c0, c1, c2 + 1)) fst fst_1 snd))

  have hfold_zero : (Array.foldl stepTriple (0, 0, 0) nums).1 = Array.count 0 nums := by
    -- list lemma
    have hlist : (nums.toList.foldl stepTriple (0, 0, 0)).1 = nums.toList.count 0 := by
      let stepNat : Nat → Nat → Nat := fun c x => if x = 0 then c + 1 else c

      have hprojFold : ∀ (l : List Nat) (acc : Nat × Nat × Nat),
          (l.foldl stepTriple acc).1 = l.foldl stepNat acc.1 := by
        intro l
        induction l with
        | nil =>
            intro acc
            simp
        | cons x xs ih =>
            intro acc
            have hfst : (stepTriple acc x).1 = stepNat acc.1 x := by
              cases acc with
              | mk a bc =>
                cases bc with
                | mk b c =>
                  by_cases hx0 : x = 0
                  · subst hx0
                    simp [stepTriple, stepNat]
                  · by_cases hx1 : x = 1
                    · subst hx1
                      simp [stepTriple, stepNat, hx0]
                    · simp [stepTriple, stepNat, hx0, hx1]
            simpa [List.foldl, hfst] using (ih (stepTriple acc x))

      have hNatFold : ∀ (l : List Nat) (k : Nat), l.foldl stepNat k = k + l.count 0 := by
        intro l
        induction l with
        | nil =>
            intro k
            simp [stepNat]
        | cons x xs ih =>
            intro k
            by_cases hx0 : x = 0
            · subst hx0
              simp [stepNat, ih, List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            · have hx0' : (x == 0) = false := by
                exact beq_false_of_ne hx0
              simp [stepNat, ih, List.count_cons, hx0, hx0', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

      -- combine without simp-rewriting `toList.foldl`
      have hproj0 : (nums.toList.foldl stepTriple (0, 0, 0)).1 = nums.toList.foldl stepNat 0 :=
        hprojFold (nums.toList) (0,0,0)
      calc
        (nums.toList.foldl stepTriple (0, 0, 0)).1
            = nums.toList.foldl stepNat 0 := hproj0
        _ = 0 + nums.toList.count 0 := by
            simpa using (hNatFold (nums.toList) 0)
        _ = nums.toList.count 0 := by simp

    -- rewrite array fold/count to list fold/count without `simp`
    have hfold_toList : Array.foldl stepTriple (0, 0, 0) nums = nums.toList.foldl stepTriple (0, 0, 0) := by
      simpa using (Array.foldl_toList (f := stepTriple) (init := (0, 0, 0)) (xs := nums)).symm
    have hcount_toList : Array.count (0 : Nat) nums = nums.toList.count 0 := by
      simpa using (Array.count_toList (xs := nums) (a := (0 : Nat))).symm

    have hfold_toList_fst : (Array.foldl stepTriple (0, 0, 0) nums).1 = (nums.toList.foldl stepTriple (0, 0, 0)).1 :=
      congrArg Prod.fst hfold_toList

    calc
      (Array.foldl stepTriple (0, 0, 0) nums).1
          = (nums.toList.foldl stepTriple (0, 0, 0)).1 := hfold_toList_fst
      _ = nums.toList.count 0 := hlist
      _ = Array.count 0 nums := hcount_toList.symm

  have hcounts1 : counts.1 = (Array.foldl stepTriple (0, 0, 0) nums).1 := by
    simpa [hcounts, stepTriple]

  calc
    c0 = counts.1 := by simpa [hc0] using hc0.symm
    _ = (Array.foldl stepTriple (0, 0, 0) nums).1 := hcounts1
    _ = Array.count 0 nums := hfold_zero

theorem correctness_goal_1
    (nums : Array ℕ)
    (counts : ℕ × ℕ × ℕ)
    (hcounts : counts =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 => if x = 0 then (c0 + 1, c1, c2) else if x = 1 then (c0, c1 + 1, c2) else (c0, c1, c2 + 1)) fst
            fst_1 snd)
    (0, 0, 0) nums)
    (c0 : ℕ)
    (c1 : ℕ)
    (c2 : ℕ)
    (hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2))
    : c1 = Array.count 1 nums := by
  classical

  -- Name the fold function from `hcounts`.
  let f : (Nat × Nat × Nat) → Nat → (Nat × Nat × Nat) :=
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 =>
              if x = 0 then (c0 + 1, c1, c2)
              else if x = 1 then (c0, c1 + 1, c2)
              else (c0, c1, c2 + 1)) fst fst_1 snd)

  have hcounts' : counts = Array.foldl f (0, 0, 0) nums := by
    simpa [f] using hcounts

  -- Extract `c1 = counts.2.1` from the projection equality.
  have hc1 : c1 = counts.2.1 := by
    have h := congrArg (fun t => t.2.1) hproj
    simpa using h.symm

  -- Main lemma: the second component of the fold counts the 1s.
  have hfold : (Array.foldl f (0, 0, 0) nums).2.1 = Array.count 1 nums := by
    -- First prove the corresponding list statement.
    have hgen : ∀ (l : List Nat) (acc : Nat × Nat × Nat),
        (l.foldl f acc).2.1 = acc.2.1 + l.count 1 := by
      intro l
      induction l with
      | nil =>
          intro acc
          simp
      | cons x xs ih =>
          intro acc
          -- One fold step.
          simp [List.foldl, ih]
          -- Analyze how the update affects the middle counter.
          have hx : (f acc x).2.1 = acc.2.1 + (if x == 1 then 1 else 0) := by
            by_cases hxeq : x = 1
            · subst hxeq
              cases acc with
              | mk a bc =>
                cases bc with
                | mk b c =>
                  simp [f, Nat.beq_refl]
            · have hxb : (x == 1) = false := (beq_eq_false_iff_ne).2 hxeq
              by_cases hx0 : x = 0
              · subst hx0
                cases acc with
                | mk a bc =>
                  cases bc with
                  | mk b c =>
                    simp [f, hxeq, hxb]
              · cases acc with
                | mk a bc =>
                  cases bc with
                  | mk b c =>
                    simp [f, hxeq, hx0, hxb]

          -- Rewrite using `hx` and `List.count_cons`.
          simp [hx, List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

    have hlist : (nums.toList.foldl f (0, 0, 0)).2.1 = nums.toList.count 1 := by
      simpa using (hgen nums.toList (0, 0, 0))

    -- Transfer back to the array.
    have hfoldl : Array.foldl f (0, 0, 0) nums = nums.toList.foldl f (0, 0, 0) := by
      simpa using (Eq.symm (Array.foldl_toList (f := f) (init := (0, 0, 0)) (xs := nums)))

    have hcount : Array.count 1 nums = nums.toList.count 1 := by
      simpa using (Eq.symm (Array.count_toList (xs := nums) (a := (1 : Nat))))

    -- Combine.
    calc
      (Array.foldl f (0, 0, 0) nums).2.1
          = (nums.toList.foldl f (0, 0, 0)).2.1 := by
              simpa using congrArg (fun t => t.2.1) hfoldl
      _ = nums.toList.count 1 := hlist
      _ = Array.count 1 nums := hcount.symm

  -- Conclude using `hc1` and `hcounts'`.
  calc
    c1 = counts.2.1 := hc1
    _ = (Array.foldl f (0, 0, 0) nums).2.1 := by simpa [hcounts']
    _ = Array.count 1 nums := hfold

theorem correctness_goal_2
    (nums : Array ℕ)
    (h_precond : precondition nums)
    (counts : ℕ × ℕ × ℕ)
    (hcounts : counts =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 => if x = 0 then (c0 + 1, c1, c2) else if x = 1 then (c0, c1 + 1, c2) else (c0, c1, c2 + 1)) fst
            fst_1 snd)
    (0, 0, 0) nums)
    (c0 : ℕ)
    (c1 : ℕ)
    (c2 : ℕ)
    (hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2))
    : c2 = Array.count 2 nums := by
  have hColors : ColorsOnly nums := by
    simpa [precondition] using h_precond

  let upd : ℕ × ℕ × ℕ → ℕ → ℕ × ℕ × ℕ := fun acc x =>
    let (c0, c1, c2) := acc
    if x = 0 then (c0 + 1, c1, c2)
    else if x = 1 then (c0, c1 + 1, c2)
    else (c0, c1, c2 + 1)

  have hcounts' : counts = Array.foldl upd (0, 0, 0) nums := by
    simpa [upd] using hcounts

  have hc2_counts : counts.2.2 = c2 := by
    have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hproj
    simpa using this

  have hc2_fold : c2 = (Array.foldl upd (0, 0, 0) nums).2.2 := by
    have : (Array.foldl upd (0, 0, 0) nums).2.2 = c2 := by
      simpa [hcounts'] using hc2_counts
    simpa using this.symm

  have eq_two_of_le_two_of_ne0_of_ne1 {x : ℕ} (hxle : x ≤ 2) (hx0 : x ≠ 0) (hx1 : x ≠ 1) : x = 2 := by
    by_contra hx2
    have : 2 < x := Nat.two_lt_of_ne hx0 hx1 hx2
    exact (not_lt_of_ge hxle) this

  have hle_toList : ∀ x : ℕ, x ∈ nums.toList → x ≤ 2 := by
    intro x hx
    have hx' : x ∈ nums := (Array.mem_toList.mp hx)
    rcases Array.getElem?_of_mem hx' with ⟨i, hi⟩
    rcases (Array.getElem?_eq_some_iff.mp hi) with ⟨hiLt, hget⟩
    have hopt : nums[i]? = some x := by
      simpa [hget] using (Array.getElem?_eq_getElem (xs := nums) hiLt)
    have hgetD : nums.getD i 0 = x := by
      simp [Array.getD_eq_getD_getElem?, hopt]
    have hbang : nums[i]! = x := by
      simpa [Array.getElem!_eq_getD, hgetD]
    have : nums[i]! ≤ 2 := hColors i hiLt
    simpa [hbang] using this

  have foldl_third_eq_count2 :
      ∀ (l : List ℕ) (acc : ℕ × ℕ × ℕ),
        (∀ x ∈ l, x ≤ 2) →
        (l.foldl upd acc).2.2 = acc.2.2 + l.count 2 := by
    intro l
    induction l with
    | nil =>
        intro acc hle
        simp
    | cons x xs ih =>
        intro acc hle
        have hxle : x ≤ 2 := hle x (by simp)
        have hleTail : ∀ y ∈ xs, y ≤ 2 := by
          intro y hy
          exact hle y (by simp [hy])

        have hupd_third : (upd acc x).2.2 = acc.2.2 + (if x = 2 then 1 else 0) := by
          rcases acc with ⟨a0, a1, a2⟩
          by_cases h0 : x = 0
          · subst h0
            simp [upd]
          · by_cases h1 : x = 1
            · subst h1
              simp [upd, h0]
            · have hx2 : x = 2 := eq_two_of_le_two_of_ne0_of_ne1 hxle h0 h1
              subst hx2
              simp [upd, h0, h1]

        calc
          ((x :: xs).foldl upd acc).2.2
              = (xs.foldl upd (upd acc x)).2.2 := by simp
          _ = (upd acc x).2.2 + xs.count 2 := by
              simpa using (ih (acc := upd acc x) hleTail)
          _ = acc.2.2 + (if x = 2 then 1 else 0) + xs.count 2 := by
              simp [hupd_third, Nat.add_assoc]
          _ = acc.2.2 + ((x :: xs).count 2) := by
              simp [List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  have hfold_third_arr : (Array.foldl upd (0, 0, 0) nums).2.2 = Array.count 2 nums := by
    have : (nums.toList.foldl upd (0, 0, 0)).2.2 = (0, 0, 0).2.2 + nums.toList.count 2 := by
      refine foldl_third_eq_count2 (l := nums.toList) (acc := (0, 0, 0)) ?_
      intro x hx
      exact hle_toList x hx
    simpa [Array.foldl_toList, Array.count_toList] using this

  calc
    c2 = (Array.foldl upd (0, 0, 0) nums).2.2 := hc2_fold
    _ = Array.count 2 nums := hfold_third_arr

theorem correctness_goal_3
    (nums : Array ℕ)
    (h_precond : precondition nums)
    (counts : ℕ × ℕ × ℕ)
    (hcounts : counts =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 => if x = 0 then (c0 + 1, c1, c2) else if x = 1 then (c0, c1 + 1, c2) else (c0, c1, c2 + 1)) fst
            fst_1 snd)
    (0, 0, 0) nums)
    (c0 : ℕ)
    (c1 : ℕ)
    (c2 : ℕ)
    (hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2))
    (n : ℕ)
    (hn : n = nums.size)
    (h_count0 : c0 = Array.count 0 nums)
    (h_count1 : c1 = Array.count 1 nums)
    (h_count2 : c2 = Array.count 2 nums)
    : c0 + c1 + c2 = n := by
  classical
  -- `counts`, `hcounts`, and `hproj` are irrelevant here: we already have the count equalities.
  subst hn

  -- A helper lemma on lists: if all entries are ≤ 2, then the counts of 0/1/2 sum to the length.
  have list_count012_eq_length :
      ∀ l : List Nat, (∀ x ∈ l, x ≤ 2) → l.count 0 + l.count 1 + l.count 2 = l.length := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons x xs ih =>
        intro h
        have hxle : x ≤ 2 := h x (by simp)
        have hxs : ∀ y ∈ xs, y ≤ 2 := by
          intro y hy
          exact h y (by simp [hy])
        have ih' : xs.count 0 + xs.count 1 + xs.count 2 = xs.length := ih hxs
        have hx012 : x = 0 ∨ x = 1 ∨ x = 2 := by
          cases x with
          | zero =>
              exact Or.inl rfl
          | succ x1 =>
              have hx1le : x1 ≤ 1 :=
                Nat.succ_le_succ_iff.1 (by simpa using hxle)
              have hx1 : x1 = 0 ∨ x1 = 1 :=
                (Nat.le_one_iff_eq_zero_or_eq_one).1 hx1le
              cases hx1 with
              | inl hx10 =>
                  subst hx10
                  exact Or.inr (Or.inl rfl)
              | inr hx11 =>
                  subst hx11
                  exact Or.inr (Or.inr rfl)
        have ih1 : (xs.count 0 + xs.count 1 + xs.count 2) + 1 = xs.length + 1 :=
          congrArg (fun t => t + 1) ih'
        cases hx012 with
        | inl hx0 =>
            subst hx0
            -- x = 0
            -- Reduce to `ih'` by reassociation/commutation of `Nat` addition.
            simpa [List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih1
        | inr hx12 =>
            cases hx12 with
            | inl hx1 =>
                subst hx1
                -- x = 1
                simpa [List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih1
            | inr hx2 =>
                subst hx2
                -- x = 2
                simpa [List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih1

  have hColors : ColorsOnly nums := by
    simpa [precondition] using h_precond

  -- Transfer the array precondition to a list-level bound on elements.
  have hleList : ∀ a ∈ nums.toList, a ≤ 2 := by
    intro a ha
    have haArr : a ∈ nums := (Array.mem_toList).1 ha
    rcases (Array.mem_iff_getElem).1 haArr with ⟨i, hi, rfl⟩
    have hle : nums[i]! ≤ 2 := hColors i hi
    have hget : nums[i]! = nums[i]'hi := by
      -- In-bounds, `getElem!` returns the same value as `getElem`.
      simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_eq_getElem, hi]
    simpa [hget] using hle

  -- Now prove the array counting identity via the list lemma.
  have hsum_counts :
      Array.count 0 nums + Array.count 1 nums + Array.count 2 nums = nums.size := by
    have hlist := list_count012_eq_length nums.toList hleList
    -- Rewrite list-counts/length as array-counts/size.
    simpa [Array.count_toList, Array.length_toList, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlist

  -- Replace `c0,c1,c2` by the corresponding `Array.count` values.
  -- Then apply `hsum_counts`.
  simpa [h_count0, h_count1, h_count2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum_counts

theorem correctness_goal_4
    (nums : Array ℕ)
    (h_precond : precondition nums)
    (counts : ℕ × ℕ × ℕ)
    (hcounts : counts =
  Array.foldl
    (fun acc x =>
      Prod.casesOn acc fun fst snd =>
        Prod.casesOn snd fun fst_1 snd =>
          (fun c0 c1 c2 => if x = 0 then (c0 + 1, c1, c2) else if x = 1 then (c0, c1 + 1, c2) else (c0, c1, c2 + 1)) fst
            fst_1 snd)
    (0, 0, 0) nums)
    (c0 : ℕ)
    (c1 : ℕ)
    (c2 : ℕ)
    (hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2))
    (n : ℕ)
    (hn : n = nums.size)
    (h_count0 : c0 = Array.count 0 nums)
    (h_count1 : c1 = Array.count 1 nums)
    (h_count2 : c2 = Array.count 2 nums)
    (h_sum : c0 + c1 + c2 = n)
    : implementation.fill c0 c1 n nums 0 = Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2 := by
    sorry

theorem correctness_goal_5
    (nums : Array ℕ)
    (c0 : ℕ)
    (c1 : ℕ)
    (c2 : ℕ)
    (n : ℕ)
    (hn : n = nums.size)
    (h_sum : c0 + c1 + c2 = n)
    (h_impl_eq : implementation.fill c0 c1 n nums 0 = Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2)
    (h_size : (implementation.fill c0 c1 n nums 0).size = nums.size)
    : Is012Sorted (implementation.fill c0 c1 n nums 0) := by
    classical
    refine ⟨c0, c0 + c1, ?_⟩
    refine And.intro (Nat.le_add_right c0 c1) ?_
    refine And.intro ?_ ?_
    · -- `c0 + c1 ≤ (fill ...).size`
      have hle_bn : c0 + c1 ≤ n := by
        have hle : c0 + c1 ≤ c0 + c1 + c2 := by
          simpa [Nat.add_assoc] using (Nat.le_add_right (c0 + c1) c2)
        simpa [h_sum] using hle
      have hle_nums : c0 + c1 ≤ nums.size := by
        simpa [hn] using hle_bn
      simpa [h_size] using hle_nums
    ·
      refine And.intro ?_ (And.intro ?_ ?_)
      · intro i hi
        have hltX : i < (Array.replicate c0 0 ++ Array.replicate c1 1).size := by
          have : i < c0 + c1 := Nat.lt_of_lt_of_le hi (Nat.le_add_right c0 c1)
          simpa [Array.size_append, Array.size_replicate] using this
        simpa [h_impl_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append,
          Array.getElem?_replicate, Array.size_append, Array.size_replicate, hltX, hi]
      · intro i hi
        have hltX : i < (Array.replicate c0 0 ++ Array.replicate c1 1).size := by
          simpa [Array.size_append, Array.size_replicate] using hi.2
        have hnot0 : ¬ i < c0 := Nat.not_lt_of_ge hi.1
        have hsub : i - c0 < c1 := by
          exact Nat.sub_lt_left_of_lt_add hi.1 hi.2
        simpa [h_impl_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append,
          Array.getElem?_replicate, Array.size_append, Array.size_replicate, hltX, hnot0, hsub]
      · intro i hi
        have hle0 : c0 ≤ i := (Nat.le_add_right c0 c1).trans hi.1
        have hnot0 : ¬ i < c0 := Nat.not_lt_of_ge hle0
        have hle1 : c1 ≤ i - c0 := by
          -- from `c0 + c1 ≤ i`
          exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hi.1)
        have hnot1 : ¬ i - c0 < c1 := Nat.not_lt_of_ge hle1
        have hi_arr : i < (Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2).size := by
          simpa [h_impl_eq] using hi.2
        have hleX : (Array.replicate c0 0 ++ Array.replicate c1 1).size ≤ i := by
          simpa [Array.size_append, Array.size_replicate] using hi.1
        have hi_lt : i < (Array.replicate c0 0 ++ Array.replicate c1 1).size + c2 := by
          simpa [Array.size_append, Array.size_replicate, Nat.add_assoc] using hi_arr
        have hsubX : i - (Array.replicate c0 0 ++ Array.replicate c1 1).size < c2 :=
          Nat.sub_lt_left_of_lt_add hleX hi_lt
        have hsub : i - c0 - c1 < c2 := by
          -- rewrite `i - (c0+c1)` to `i - c0 - c1`
          simpa [Array.size_append, Array.size_replicate, Nat.sub_sub, Nat.add_assoc] using hsubX
        simpa [h_impl_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append,
          Array.getElem?_replicate, Array.size_append, Array.size_replicate, hnot0, hnot1, hsub]

theorem correctness_goal
    (nums : Array Nat)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical
  unfold precondition at h_precond
  unfold postcondition countVal
  simp [implementation]
  set counts : Nat × Nat × Nat :=
    nums.foldl
      (fun (acc : Nat × Nat × Nat) x =>
        let (c0, c1, c2) := acc
        if x = 0 then (c0 + 1, c1, c2)
        else if x = 1 then (c0, c1 + 1, c2)
        else (c0, c1, c2 + 1))
      (0, 0, 0) with hcounts
  set c0 : Nat := counts.1
  set c1 : Nat := counts.2.1
  set c2 : Nat := counts.2.2
  have hproj : (counts.1, counts.2.1, counts.2.2) = (c0, c1, c2) := by
    simp [c0, c1, c2]
  set n : Nat := nums.size with hn

  have h_count0 : c0 = nums.count 0 := by expose_names; exact (correctness_goal_0 nums counts hcounts c0 c1 c2 hproj)
  have h_count1 : c1 = nums.count 1 := by expose_names; exact (correctness_goal_1 nums counts hcounts c0 c1 c2 hproj)
  have h_count2 : c2 = nums.count 2 := by expose_names; exact (correctness_goal_2 nums h_precond counts hcounts c0 c1 c2 hproj)
  have h_sum : c0 + c1 + c2 = n := by
    -- use hn to relate n to nums.size
    expose_names; exact (correctness_goal_3 nums h_precond counts hcounts c0 c1 c2 hproj n hn h_count0 h_count1 h_count2)

  have h_impl_eq :
      implementation.fill c0 c1 n nums 0
        = Array.replicate c0 0 ++ Array.replicate c1 1 ++ Array.replicate c2 2 := by
    expose_names; exact (correctness_goal_4 nums h_precond counts hcounts c0 c1 c2 hproj n hn h_count0 h_count1 h_count2 h_sum)

  have h_size : (implementation.fill c0 c1 n nums 0).size = nums.size := by
    expose_names; intros; expose_names; try simp_all; try grind
  have h_sorted : Is012Sorted (implementation.fill c0 c1 n nums 0) := by
    expose_names; exact (correctness_goal_5 nums c0 c1 c2 n hn h_sum h_impl_eq h_size)
  have h_c0 : (implementation.fill c0 c1 n nums 0).count 0 = nums.count 0 := by
    expose_names; intros; expose_names; try simp_all; try grind
  have h_c1 : (implementation.fill c0 c1 n nums 0).count 1 = nums.count 1 := by
    expose_names; intros; expose_names; try simp_all; try grind
  have h_c2 : (implementation.fill c0 c1 n nums 0).count 2 = nums.count 2 := by
    expose_names; intros; expose_names; try simp_all; try grind

  exact And.intro h_size (And.intro h_sorted (And.intro h_c0 (And.intro h_c1 h_c2)))
end Proof
