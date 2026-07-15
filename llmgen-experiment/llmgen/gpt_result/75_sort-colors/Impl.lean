import Velvet.Std
import Extensions.Tactics
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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

section Specs
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
method SortColors (nums : Array Nat)
  return (result : Array Nat)
  require precondition nums
  ensures postcondition nums result
  do
    -- Count 0s, 1s, 2s in one pass
    let mut c0 : Nat := 0
    let mut c1 : Nat := 0
    let mut c2 : Nat := 0

    let mut i : Nat := 0
    while i < nums.size
      -- i stays within bounds
      invariant "count_i_bounds" i ≤ nums.size
      -- counters match counts in the processed prefix nums[0..i)
      invariant "count_c0" c0 = countVal (nums.extract 0 i) 0
      invariant "count_c1" c1 = countVal (nums.extract 0 i) 1
      invariant "count_c2" c2 = countVal (nums.extract 0 i) 2
      -- every processed element contributes to exactly one counter
      invariant "count_sum" c0 + c1 + c2 = i
      decreasing nums.size - i
    do
      let v := nums[i]!
      if v = 0 then
        c0 := c0 + 1
      else
        if v = 1 then
          c1 := c1 + 1
        else
          -- By precondition, v ≤ 2 and not 0/1, so it must be 2
          c2 := c2 + 1
      i := i + 1

    -- Build result array in-place style (O(1) aux besides counters):
    -- fill first c0 entries with 0, next c1 with 1, remaining with 2.
    let mut res : Array Nat := Array.replicate nums.size 0
    let mut j : Nat := 0
    while j < nums.size
      invariant "build_res_size" res.size = nums.size
      invariant "build_j_bounds" j ≤ nums.size
      -- prefix already written is exactly the target 0/1/2 partition
      invariant "build_prefix_0" (∀ k : Nat, k < j ∧ k < c0 → res[k]! = 0)
      invariant "build_prefix_1" (∀ k : Nat, k < j ∧ c0 ≤ k ∧ k < c0 + c1 → res[k]! = 1)
      invariant "build_prefix_2" (∀ k : Nat, k < j ∧ c0 + c1 ≤ k → res[k]! = 2)
      decreasing nums.size - j
    do
      if j < c0 then
        res := res.set! j 0
      else
        if j < c0 + c1 then
          res := res.set! j 1
        else
          res := res.set! j 2
      j := j + 1

    return res
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

#assert_same_evaluation #[((SortColors test1_nums).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((SortColors test2_nums).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((SortColors test3_nums).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((SortColors test4_nums).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((SortColors test5_nums).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((SortColors test6_nums).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((SortColors test7_nums).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((SortColors test8_nums).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((SortColors test9_nums).run), DivM.res test9_Expected ]
end Assertions

section Pbt
velvet_plausible_test SortColors (config := { maxMs := some 20000 })
end Pbt

section Proof
set_option maxHeartbeats 10000000

theorem goal_0
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) + OfNat.ofNat 1 = Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  have hget : nums[i]! = nums[i] := by
    -- in-bounds, `getElem!` returns the actual element
    simp [Array.getElem!_eq_getD, Array.getD, if_pos]

  have hi : nums[i] = 0 := by
    simpa [hget] using if_pos_1

  have hpush : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
    -- `extract 0 (i+1)` is the previous prefix with the next element appended
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem Nat nums 0 i if_pos)

  calc
    Array.count 0 (nums.extract 0 i) + 1
        = Array.count 0 ((nums.extract 0 i).push 0) := by
            simpa using
              (Array.count_push_self (a := (0 : Nat)) (xs := nums.extract 0 i)).symm
    _   = Array.count 0 ((nums.extract 0 i).push nums[i]) := by
            simpa [hi]
    _   = Array.count 0 (nums.extract 0 (i + 1)) := by
            simpa [hpush]

theorem goal_1
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  have hsome : nums[i]? = some (nums[i]'if_pos) := by
    refine (Array.getElem?_eq_some_iff (xs := nums) (i := i) (b := (nums[i]'if_pos))).2 ?_
    exact ⟨if_pos, rfl⟩

  have hbang : nums[i]! = (nums[i]'if_pos) := by
    calc
      nums[i]! = nums.getD i default := by
        simpa [Array.getElem!_eq_getD]
      _ = nums[i]?.getD default := by
        simpa using
          (Array.getD_eq_getD_getElem? (xs := nums) (i := i) (d := (default : Nat)))
      _ = (nums[i]'if_pos) := by
        simp [hsome]

  have hi0 : (nums[i]'if_pos) = 0 := by
    simpa [hbang] using if_pos_1

  have hne : (nums[i]'if_pos) ≠ (1 : Nat) := by
    simpa [hi0]

  have hextract : (nums.extract 0 i).push (nums[i]'if_pos) = nums.extract 0 (i + 1) := by
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem Nat nums 0 i if_pos)

  -- rewrite the longer prefix as a push of the new element
  -- and use that pushing a non-1 element does not change the count of 1s.
  -- (Also normalize numeric literals in the goal.)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (show Array.count (1 : Nat) (nums.extract 0 i) = Array.count (1 : Nat) (nums.extract 0 (i + 1)) from by
      rw [← hextract]
      exact (Array.count_push_of_ne (xs := nums.extract 0 i) (a := (1 : Nat)) (b := (nums[i]'if_pos)) hne).symm)

theorem goal_2
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 0)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  have hi : i < nums.size := if_pos

  have main : Array.count (2 : Nat) (nums.extract 0 i) = Array.count (2 : Nat) (nums.extract 0 (i + 1)) := by
    -- Relate `getElem!` and `getElem` when we have an in-bounds proof.
    have hgetEq : nums[i]! = nums[i] := by
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, hi]

    have hget : nums[i] = (0 : Nat) := by
      simpa [hgetEq] using if_pos_1

    have hne : nums[i] ≠ (2 : Nat) := by
      simpa [hget] using (show (0 : Nat) ≠ (2 : Nat) from by decide)

    have hcountPush : Array.count (2 : Nat) ((nums.extract 0 i).push nums[i]) =
        Array.count (2 : Nat) (nums.extract 0 i) :=
      Array.count_push_of_ne (xs := nums.extract 0 i) (a := (2 : Nat)) (b := nums[i]) hne

    have hextract : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
      -- `extract 0 (i+1)` is the old prefix with the `i`th element appended.
      simpa [Nat.min_eq_left (Nat.zero_le i)] using
        (@Array.push_extract_getElem Nat nums 0 i hi)

    calc
      Array.count (2 : Nat) (nums.extract 0 i)
          = Array.count (2 : Nat) ((nums.extract 0 i).push nums[i]) := by
              simpa using (Eq.symm hcountPush)
      _ = Array.count (2 : Nat) (nums.extract 0 (i + 1)) := by
              simpa [hextract]

  simpa using main

theorem goal_3
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  -- show `get!` coincides with safe indexing for an in-bounds index
  have hget : nums[i]! = nums[i] := by
    have hopt : nums[i]? = some nums[i] := by
      apply (Array.getElem?_eq_some_iff (xs := nums) (i := i) (b := nums[i])).2
      exact ⟨if_pos, rfl⟩
    simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hopt]

  have hne : nums[i] ≠ (0 : Nat) := by
    intro h
    apply if_neg
    simpa [hget, h]

  have hpush : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem Nat nums 0 i if_pos)

  have hcount : Array.count 0 ((nums.extract 0 i).push nums[i]) = Array.count 0 (nums.extract 0 i) := by
    exact
      (Array.count_push_of_ne (xs := nums.extract 0 i) (a := (0 : Nat)) (b := nums[i]) hne)

  calc
    Array.count 0 (nums.extract 0 i)
        = Array.count 0 ((nums.extract 0 i).push nums[i]) := by
            simpa using hcount.symm
    _ = Array.count 0 (nums.extract 0 (i + 1)) := by
            simpa [hpush]

theorem goal_4
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) + OfNat.ofNat 1 = Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  -- express the (i+1)-prefix as pushing the i-th element onto the i-prefix
  have hpush : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem Nat nums 0 i if_pos)

  -- convert the hypothesis about `getElem!` into one about `getElem`
  have hget! : nums[i]! = nums[i] := by
    classical
    -- `getElem!` is `getD` at the same index
    simp [Array.getElem!_eq_getD]
    -- now show the `getD` is the in-bounds element
    -- `nums[i]?` is `some nums[i]` when `i < nums.size`
    have hopt : nums[i]? = some nums[i] :=
      (Array.getElem?_eq_some_getElem_iff nums i if_pos).2 trivial
    -- unfold `getD`
    simp [Array.getD, hopt]

  have hi : nums[i] = (1 : Nat) := by
    simpa [hget!] using if_pos_1

  -- now use the `count_push` formula
  calc
    Array.count (1 : Nat) (nums.extract 0 i) + 1
        = Array.count (1 : Nat) (nums.extract 0 i) + (if nums[i] = (1 : Nat) then 1 else 0) := by
            simp [hi]
    _ = Array.count (1 : Nat) (nums.extract 0 (i + 1)) := by
            -- rewrite `extract 0 (i+1)` as a push, then apply `count_push`
            simpa [hpush] using
              (Array.count_push (a := (1 : Nat)) (b := nums[i]) (xs := nums.extract 0 i) |>.symm)

theorem goal_5
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_pos_1 : nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  -- Convert `get!` at an in-bounds index to `getElem`.
  have h_getBang : nums[i]! = nums[i]'if_pos := by
    simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?, if_pos]

  have h_get : nums[i]'if_pos = (1 : Nat) := by
    simpa [h_getBang] using if_pos_1

  have hne : nums[i]'if_pos ≠ (2 : Nat) := by
    simpa [h_get]

  -- `extract 0 (i+1)` is obtained by pushing `nums[i]` onto `extract 0 i`.
  have hpush : (nums.extract 0 i).push (nums[i]'if_pos) = nums.extract 0 (i + 1) := by
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem Nat nums 0 i if_pos)

  -- Since the pushed element is not `2`, the count of `2` does not change.
  calc
    Array.count (2 : Nat) (nums.extract 0 i)
        = Array.count (2 : Nat) ((nums.extract 0 i).push (nums[i]'if_pos)) := by
            exact (Array.count_push_of_ne (xs := nums.extract 0 i)
              (a := (2 : Nat)) (b := nums[i]'if_pos) hne).symm
    _ = Array.count (2 : Nat) (nums.extract 0 (i + 1)) := by
          simpa [hpush]

theorem goal_6
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    : Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 0) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
    intros; expose_names; exact goal_3 nums i if_pos if_neg

theorem goal_7
    (nums : Array ℕ)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg_1 : ¬nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) i) = Array.count (OfNat.ofNat 1) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  -- Relate `get!` and `getElem` at an in-bounds index
  have hget : nums[i]! = nums[i]'if_pos := by
    simpa using (getElem!_pos nums i if_pos)

  -- The element appended is not `1`
  have hne1 : nums[i]'if_pos ≠ (1 : Nat) := by
    intro h
    apply if_neg_1
    calc
      nums[i]! = nums[i]'if_pos := hget
      _ = 1 := h

  -- Extending the prefix by one element is the same as pushing `nums[i]`
  have hpush : (nums.extract 0 i).push (nums[i]'if_pos) = nums.extract 0 (i + 1) := by
    -- use an explicit application to avoid the binder name `as`
    simpa [Nat.min_eq_left (Nat.zero_le i)] using
      (@Array.push_extract_getElem Nat nums 0 i if_pos)

  -- Count of `1` does not change when pushing a non-`1`
  have hcount :
      Array.count (1 : Nat) ((nums.extract 0 i).push (nums[i]'if_pos)) =
        Array.count (1 : Nat) (nums.extract 0 i) := by
    simpa using
      (Array.count_push_of_ne (xs := nums.extract 0 i) (a := (1 : Nat)) (b := nums[i]'if_pos) hne1)

  -- Finish by rewriting `extract 0 (i+1)` as the pushed prefix
  calc
    Array.count (1 : Nat) (nums.extract 0 i)
        = Array.count (1 : Nat) ((nums.extract 0 i).push (nums[i]'if_pos)) := by
            simpa using hcount.symm
    _ = Array.count (1 : Nat) (nums.extract 0 (i + 1)) := by
            simpa [hpush]

theorem goal_8
    (nums : Array ℕ)
    (require_1 : precondition nums)
    (i : ℕ)
    (if_pos : i < nums.size)
    (if_neg : ¬nums[i]! = OfNat.ofNat 0)
    (if_neg_1 : ¬nums[i]! = OfNat.ofNat 1)
    : Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) i) + OfNat.ofNat 1 = Array.count (OfNat.ofNat 2) (nums.extract (OfNat.ofNat 0) (i + OfNat.ofNat 1)) := by
  -- We'll prove the simp-normalized statement.
  have hGoal : Array.count (2 : Nat) (nums.extract 0 i) + 1 = Array.count (2 : Nat) (nums.extract 0 (i + 1)) := by
    -- From the precondition, all entries are ≤ 2.
    have hColors : ColorsOnly nums := by
      simpa [precondition] using require_1
    have hi_le2 : nums[i]! ≤ (2 : Nat) := hColors i if_pos

    -- Since nums[i] is not 0 and not 1, it must be 2.
    have hi_eq2_bang : nums[i]! = (2 : Nat) := by
      have hlt_or_eq2 : nums[i]! < 2 ∨ nums[i]! = 2 := Nat.lt_or_eq_of_le hi_le2
      cases hlt_or_eq2 with
      | inr hEq2 =>
          exact hEq2
      | inl hlt2 =>
          have hle1 : nums[i]! ≤ 1 := by
            exact (Nat.lt_succ_iff.mp (by simpa using hlt2))
          have hlt_or_eq1 : nums[i]! < 1 ∨ nums[i]! = 1 := Nat.lt_or_eq_of_le hle1
          cases hlt_or_eq1 with
          | inr hEq1 =>
              have : False := if_neg_1 (by simpa using hEq1)
              cases this
          | inl hlt1 =>
              have hle0 : nums[i]! ≤ 0 := by
                exact (Nat.lt_succ_iff.mp (by simpa using hlt1))
              have hEq0 : nums[i]! = 0 := Nat.eq_zero_of_le_zero hle0
              have : False := if_neg (by simpa using hEq0)
              cases this

    -- Convert getElem! to getElem since we know i is in bounds.
    have hi_bang_eq_get : nums[i]! = nums[i] := by
      calc
        nums[i]! = nums.getD i default := by
          simpa using (Array.getElem!_eq_getD (xs := nums) (i := i))
        _ = nums[i]?.getD default := by
          simpa using (Array.getD_eq_getD_getElem? (xs := nums) (i := i) (d := (default : Nat)))
        _ = nums[i] := by
          -- in bounds, getElem? returns `some (getElem ...)`
          simpa using congrArg (fun o => o.getD (default : Nat)) (Array.getElem?_eq_getElem (xs := nums) (i := i) if_pos)

    have hi_eq2 : nums[i] = (2 : Nat) := by
      simpa [hi_bang_eq_get] using hi_eq2_bang

    -- Relate the (i+1)-prefix to pushing nums[i] onto the i-prefix.
    have hpush_extract : (nums.extract 0 i).push nums[i] = nums.extract 0 (i + 1) := by
      simpa using (Array.push_extract_getElem (i := (0 : Nat)) (j := i) if_pos)

    have hcnt_push : Array.count (2 : Nat) ((nums.extract 0 i).push nums[i]) = Array.count (2 : Nat) ((nums.extract 0 i).push (2 : Nat)) := by
      simp [hi_eq2]

    calc
      Array.count (2 : Nat) (nums.extract 0 i) + 1
          = Array.count (2 : Nat) ((nums.extract 0 i).push (2 : Nat)) := by
              simpa using
                ((Array.count_push_self (a := (2 : Nat)) (xs := nums.extract 0 i)).symm)
      _ = Array.count (2 : Nat) ((nums.extract 0 i).push nums[i]) := by
            simpa using hcnt_push.symm
      _ = Array.count (2 : Nat) (nums.extract 0 (i + 1)) := by
            simpa [hpush_extract]

  simpa using hGoal

theorem getBang_eq_getElem (xs : Array Nat) (i : Nat) (h : i < xs.size) :
        xs[i]! = xs[i]'h := by
      -- `getElem!` is implemented via `getD` and `getElem?`
      simp [Array.getElem!_eq_getD, Array.getD, Array.getElem?_eq_getElem h, h]

set_option maxHeartbeats 2000000 in

theorem goal_9
    (nums : Array ℕ)
    (require_1 : precondition nums)
    (i_4 : ℕ)
    (i_6 : ℕ)
    (res_1 : Array ℕ)
    (invariant_count_i_bounds : i_4 ≤ nums.size)
    (done_1 : ¬i_4 < nums.size)
    (invariant_count_sum : countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) + countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 1) + countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 2) = i_4)
    (invariant_build_j_bounds : i_6 ≤ nums.size)
    (done_2 : ¬i_6 < nums.size)
    (invariant_build_res_size : res_1.size = nums.size)
    (invariant_build_prefix_0 : ∀ k < i_6, k < countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) → res_1[k]! = OfNat.ofNat 0)
    (invariant_build_prefix_1 : ∀ k < i_6, countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) ≤ k → k < countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) + countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 1) → res_1[k]! = OfNat.ofNat 1)
    (invariant_build_prefix_2 : ∀ k < i_6, countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 0) + countVal (nums.extract (OfNat.ofNat 0) i_4) (OfNat.ofNat 1) ≤ k → res_1[k]! = OfNat.ofNat 2)
    : postcondition nums res_1 := by

  -- derive loop indices are at the end
  have hi4_ge : nums.size ≤ i_4 := by
    exact le_of_not_gt (by simpa [gt_iff_lt] using done_1)
  have hi4 : i_4 = nums.size := Nat.le_antisymm invariant_count_i_bounds hi4_ge

  have hi6_ge : nums.size ≤ i_6 := by
    exact le_of_not_gt (by simpa [gt_iff_lt] using done_2)
  have hi6 : i_6 = nums.size := Nat.le_antisymm invariant_build_j_bounds hi6_ge

  -- name the final counters
  set c0 : Nat := countVal (nums.extract 0 i_4) 0 with hc0
  set c1 : Nat := countVal (nums.extract 0 i_4) 1 with hc1
  set c2 : Nat := countVal (nums.extract 0 i_4) 2 with hc2

  have hsum : c0 + c1 + c2 = i_4 := by
    simpa [hc0, hc1, hc2] using invariant_count_sum

  have h_extract : nums.extract 0 i_4 = nums := by
    apply Array.extract_eq_self_of_le
    simpa [hi4] using hi4_ge

  have hc0_nums : c0 = countVal nums 0 := by simpa [hc0, h_extract]
  have hc1_nums : c1 = countVal nums 1 := by simpa [hc1, h_extract]
  have hc2_nums : c2 = countVal nums 2 := by simpa [hc2, h_extract]

  -- build the explicit target array
  let xs0 : Array Nat := Array.replicate c0 0
  let xs1 : Array Nat := Array.replicate c1 1
  let xs2 : Array Nat := Array.replicate c2 2
  let target : Array Nat := xs0 ++ (xs1 ++ xs2)

  have htarget_size : target.size = nums.size := by
    have : target.size = c0 + c1 + c2 := by
      simp [target, xs0, xs1, xs2, Array.size_append, Nat.add_assoc]
    calc
      target.size = c0 + c1 + c2 := this
      _ = i_4 := by simpa [Nat.add_assoc] using hsum
      _ = nums.size := hi4

  have hres_target_size : res_1.size = target.size := by
    calc
      res_1.size = nums.size := invariant_build_res_size
      _ = target.size := by simpa [htarget_size]

  -- show `res_1` is exactly `target`
  have hres_eq_target : res_1 = target := by
    apply Array.ext hres_target_size
    intro i hi_res hi_tgt

    have hiN : i < nums.size := by simpa [invariant_build_res_size] using hi_res
    have hi_i6 : i < i_6 := by simpa [hi6] using hiN

    by_cases h0 : i < c0
    · -- first block
      have hres0_bang : res_1[i]! = 0 :=
        invariant_build_prefix_0 i hi_i6 (by simpa [hc0] using h0)
      have hres0 : res_1[i]'hi_res = 0 := by
        simpa [getBang_eq_getElem res_1 i hi_res] using hres0_bang

      have ht0 : target[i]'hi_tgt = 0 := by
        have houter : target[i]'hi_tgt = xs0[i]'(by simpa [xs0] using h0) := by
          simpa [target] using
            (Array.getElem_append_left (xs := xs0) (ys := (xs1 ++ xs2)) (i := i)
              (h := by simpa [target] using hi_tgt) (hlt := by simpa [xs0] using h0))
        have hrep : xs0[i]'(by simpa [xs0] using h0) = 0 := by
          simpa [xs0] using
            (Array.getElem_replicate (n := c0) (v := (0 : Nat)) (i := i)
              (h := by simpa [xs0] using h0))
        simpa [houter] using hrep

      simpa [hres0, ht0]

    · have hge0 : c0 ≤ i := Nat.le_of_not_gt h0
      by_cases h1 : i < c0 + c1
      · -- middle block
        have hres1_bang : res_1[i]! = 1 :=
          invariant_build_prefix_1 i hi_i6 (by simpa [hc0] using hge0) (by simpa [hc0, hc1] using h1)
        have hres1 : res_1[i]'hi_res = 1 := by
          simpa [getBang_eq_getElem res_1 i hi_res] using hres1_bang

        have hlt1 : i - c0 < c1 :=
          Nat.sub_lt_left_of_lt_add hge0 (by simpa [Nat.add_assoc] using h1)

        have ht1 : target[i]'hi_tgt = 1 := by
          have hx0 : xs0.size = c0 := by simp [xs0]
          have houter : target[i]'hi_tgt = (xs1 ++ xs2)[i - c0]'(by
              have : i - c0 < c1 + c2 :=
                Nat.sub_lt_left_of_lt_add hge0 (by
                  simpa [target, xs0, xs1, xs2, Array.size_append, Nat.add_assoc] using hi_tgt)
              simpa [xs1, xs2, Array.size_append] using this) := by
            simpa [target, hx0] using
              (Array.getElem_append_right (xs := xs0) (ys := xs1 ++ xs2) (i := i)
                (h := by simpa [target] using hi_tgt) (hle := by simpa [xs0] using hge0))

          have hinSize : i - c0 < (xs1 ++ xs2).size := by
            have hle : xs1.size ≤ (xs1 ++ xs2).size := by
              simp [xs1, xs2, Array.size_append, Nat.le_add_right]
            exact lt_of_lt_of_le (by simpa [xs1] using hlt1) hle

          have hin : (xs1 ++ xs2)[i - c0]'hinSize = xs1[i - c0]'(by simpa [xs1] using hlt1) := by
            simpa using
              (Array.getElem_append_left (xs := xs1) (ys := xs2) (i := i - c0)
                (h := hinSize) (hlt := by simpa [xs1] using hlt1))

          have hrep : xs1[i - c0]'(by simpa [xs1] using hlt1) = 1 := by
            simpa [xs1] using
              (Array.getElem_replicate (n := c1) (v := (1 : Nat)) (i := i - c0)
                (h := by simpa [xs1] using hlt1))

          simpa [houter] using (hin.trans hrep)

        simpa [hres1, ht1]

      · -- last block
        have hge1 : c0 + c1 ≤ i := Nat.le_of_not_gt h1

        have hres2_bang : res_1[i]! = 2 :=
          invariant_build_prefix_2 i hi_i6 (by simpa [hc0, hc1] using hge1)
        have hres2 : res_1[i]'hi_res = 2 := by
          simpa [getBang_eq_getElem res_1 i hi_res] using hres2_bang

        have hj_lt : i - c0 < c1 + c2 :=
          Nat.sub_lt_left_of_lt_add hge0 (by
            simpa [target, xs0, xs1, xs2, Array.size_append, Nat.add_assoc] using hi_tgt)

        have hgej : c1 ≤ i - c0 := by
          have h' : c1 + c0 ≤ i := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hge1
          have h'' : c1 + c0 ≤ (i - c0) + c0 := by
            simpa [Nat.sub_add_cancel hge0] using h'
          exact Nat.le_of_add_le_add_right h''

        have hlt2 : (i - c0) - c1 < c2 :=
          Nat.sub_lt_left_of_lt_add hgej (by simpa [Nat.add_assoc] using hj_lt)

        have ht2 : target[i]'hi_tgt = 2 := by
          have hx0 : xs0.size = c0 := by simp [xs0]
          have hs1 : xs1.size = c1 := by simp [xs1]
          have houter : target[i]'hi_tgt = (xs1 ++ xs2)[i - c0]'(by
              simpa [xs1, xs2, Array.size_append] using hj_lt) := by
            simpa [target, hx0] using
              (Array.getElem_append_right (xs := xs0) (ys := xs1 ++ xs2) (i := i)
                (h := by simpa [target] using hi_tgt) (hle := by simpa [xs0] using hge0))

          have hinSize : i - c0 < (xs1 ++ xs2).size := by
            simpa [xs1, xs2, Array.size_append] using hj_lt

          have hin : (xs1 ++ xs2)[i - c0]'hinSize =
              xs2[(i - c0) - xs1.size]'(by
                simpa [hs1, xs2] using hlt2) := by
            simpa [hs1] using
              (Array.getElem_append_right (xs := xs1) (ys := xs2) (i := i - c0)
                (h := hinSize) (hle := by simpa [xs1] using hgej))

          have hrep : xs2[(i - c0) - xs1.size]'(by simpa [hs1, xs2] using hlt2) = 2 := by
            simpa [xs2, hs1] using
              (Array.getElem_replicate (n := c2) (v := (2 : Nat)) (i := (i - c0) - c1)
                (h := by simpa [xs2] using hlt2))

          simpa [houter] using (hin.trans hrep)

        simpa [hres2, ht2]

  -- Now discharge the postcondition
  unfold postcondition
  refine ⟨invariant_build_res_size, ?_, ?_, ?_, ?_⟩

  · -- Is012Sorted
    unfold Is012Sorted
    refine ⟨c0, c0 + c1, ?_⟩
    refine ⟨Nat.le_add_right c0 c1, ?_, ?_, ?_, ?_⟩
    · -- b ≤ size
      have hle : c0 + c1 ≤ i_4 := by
        have : c0 + c1 ≤ c0 + c1 + c2 := Nat.le_add_right (c0 + c1) c2
        simpa [Nat.add_assoc, hsum] using this
      simpa [invariant_build_res_size, hi4] using hle

    · -- zeros
      intro i hi
      have hi_lt_size : i < nums.size := lt_of_lt_of_le hi (by
        have : c0 ≤ c0 + c1 + c2 := by
          simpa [Nat.add_assoc] using Nat.le_add_right c0 (c1 + c2)
        simpa [hsum, hi4] using this)
      have hi_i6 : i < i_6 := by simpa [hi6] using hi_lt_size
      exact invariant_build_prefix_0 i hi_i6 (by simpa [hc0] using hi)

    · -- ones
      intro i hi
      rcases hi with ⟨hia, hib⟩
      have hi_lt_size : i < nums.size := lt_of_lt_of_le hib (by
        have hle : c0 + c1 ≤ i_4 := by
          have : c0 + c1 ≤ c0 + c1 + c2 := Nat.le_add_right (c0 + c1) c2
          simpa [Nat.add_assoc, hsum] using this
        simpa [hi4] using hle)
      have hi_i6 : i < i_6 := by simpa [hi6] using hi_lt_size
      exact invariant_build_prefix_1 i hi_i6 (by simpa [hc0] using hia) (by simpa [hc0, hc1] using hib)

    · -- twos
      intro i hi
      rcases hi with ⟨hib, his⟩
      have hi_i6 : i < i_6 := by
        have : i < nums.size := by simpa [invariant_build_res_size] using his
        simpa [hi6] using this
      exact invariant_build_prefix_2 i hi_i6 (by simpa [hc0, hc1] using hib)

  · -- count 0
    have : countVal res_1 0 = c0 := by
      simp [countVal, hres_eq_target, target, xs0, xs1, xs2,
        Array.count_append, Array.count_replicate, Array.count_replicate_self]
    simpa [hc0_nums] using this

  · -- count 1
    have : countVal res_1 1 = c1 := by
      simp [countVal, hres_eq_target, target, xs0, xs1, xs2,
        Array.count_append, Array.count_replicate, Array.count_replicate_self]
    simpa [hc1_nums] using this

  · -- count 2
    have : countVal res_1 2 = c2 := by
      simp [countVal, hres_eq_target, target, xs0, xs1, xs2,
        Array.count_append, Array.count_replicate, Array.count_replicate_self]
    simpa [hc2_nums] using this


prove_correct SortColors by
  loom_solve <;> (try injections; try subst_vars; try (conv => congr <;> simp) ; try expose_names)
  exact (goal_0 nums i if_pos if_pos_1)
  exact (goal_1 nums i if_pos if_pos_1)
  exact (goal_2 nums i if_pos if_pos_1)
  exact (goal_3 nums i if_pos if_neg)
  exact (goal_4 nums i if_pos if_pos_1)
  exact (goal_5 nums i if_pos if_pos_1)
  exact (goal_6 nums i if_pos if_neg)
  exact (goal_7 nums i if_pos if_neg_1)
  exact (goal_8 nums require_1 i if_pos if_neg if_neg_1)
  exact (goal_9 nums require_1 i_4 i_6 res_1 invariant_count_i_bounds done_1 invariant_count_sum invariant_build_j_bounds done_2 invariant_build_res_size invariant_build_prefix_0 invariant_build_prefix_1 invariant_build_prefix_2)
end Proof
