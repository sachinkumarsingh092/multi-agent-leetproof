import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    217. Contains Duplicate: Determine whether an integer array contains any value at least twice.
    **Important: complexity should be O(n^2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array of integers `nums`.
    2. The output is a boolean.
    3. The output is `true` exactly when there exist two different indices i and j with i < j such that nums[i] = nums[j].
    4. The output is `false` exactly when for all indices i < j in range, nums[i] ≠ nums[j] (all elements are distinct).
    5. Edge cases: empty arrays and single-element arrays have no duplicates, so the result is false.
-/

-- There is a duplicate iff two different indices within bounds have equal elements.
def HasDuplicate (nums : Array Int) : Prop :=
  ∃ (i : Nat) (j : Nat), i < j ∧ j < nums.size ∧ nums[i]! = nums[j]!

def precondition (nums : Array Int) : Prop :=
  True

def postcondition (nums : Array Int) (result : Bool) : Prop :=
  (result = true ↔ HasDuplicate nums) ∧
  (result = false ↔ ¬ HasDuplicate nums)
end Specs

section Impl
def implementation (nums : Array Int) : Bool :=
  let rec outer (i : Nat) : Bool :=
    if hi : i < nums.size then
      let xi := nums[i]!
      let rec inner (j : Nat) : Bool :=
        if hj : j < nums.size then
          if xi = nums[j]! then
            true
          else
            inner (j + 1)
        else
          false
      if inner (i + 1) then
        true
      else
        outer (i + 1)
    else
      false
  outer 0
end Impl

section TestCases
-- Test case 1: example 1
-- nums = [1,2,3,1] -> true

def test1_nums : Array Int := #[1, 2, 3, 1]
def test1_Expected : Bool := true

-- Test case 2: example 2
-- nums = [1,2,3,4] -> false

def test2_nums : Array Int := #[1, 2, 3, 4]
def test2_Expected : Bool := false

-- Test case 3: example 3 (multiple duplicates)

def test3_nums : Array Int := #[1, 1, 1, 3, 3, 4, 3, 2, 4, 2]
def test3_Expected : Bool := true

-- Test case 4: empty array

def test4_nums : Array Int := #[]
def test4_Expected : Bool := false

-- Test case 5: singleton array

def test5_nums : Array Int := #[42]
def test5_Expected : Bool := false

-- Test case 6: duplicates adjacent

def test6_nums : Array Int := #[7, 7]
def test6_Expected : Bool := true

-- Test case 7: duplicates non-adjacent with negatives

def test7_nums : Array Int := #[-1, 0, 1, 2, -1]
def test7_Expected : Bool := true

-- Test case 8: all distinct including negative and zero

def test8_nums : Array Int := #[-3, -2, -1, 0, 1, 2, 3]
def test8_Expected : Bool := false

-- Test case 9: many equal elements

def test9_nums : Array Int := #[5, 5, 5, 5]
def test9_Expected : Bool := true
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

section Proof
theorem correctness_goal_0
    (nums : Array ℤ)
    : implementation.outer nums 0 = true ↔ HasDuplicate nums := by
  classical

  have inner_spec :
      ∀ (xi : ℤ) (j : Nat),
        implementation.outer.inner nums xi j = true ↔
          ∃ k, j ≤ k ∧ k < nums.size ∧ xi = nums[k]! := by
    intro xi j
    generalize hm : nums.size - j = m
    induction m generalizing j with
    | zero =>
        have hle : nums.size ≤ j := by
          by_contra hlt
          have hj : j < nums.size := Nat.lt_of_not_ge hlt
          have hpos : 0 < nums.size - j := Nat.sub_pos_of_lt hj
          simpa [hm] using hpos
        have hjFalse : ¬ j < nums.size := Nat.not_lt_of_ge hle
        unfold implementation.outer.inner
        -- dependent-if rewrite
        rw [dif_neg hjFalse]
        constructor
        · intro h
          simpa using h
        · rintro ⟨k, hjk, hk, _⟩
          exact (Nat.not_lt_of_ge (le_trans hle hjk) hk).elim

    | succ m ih =>
        have hj : j < nums.size := by
          by_contra hnj
          have hle : nums.size ≤ j := Nat.le_of_not_gt hnj
          have hsub : nums.size - j = 0 := Nat.sub_eq_zero_of_le hle
          have : m.succ = 0 := by simpa [hm] using hsub
          exact (Nat.succ_ne_zero m) this

        have hm' : nums.size - (j + 1) = m := by
          simpa [Nat.sub_succ, hm, Nat.succ_sub_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

        unfold implementation.outer.inner
        rw [dif_pos hj]
        by_cases hEq : xi = nums[j]!
        · rw [if_pos hEq]
          constructor
          · intro _
            exact ⟨j, le_rfl, hj, hEq⟩
          · intro _
            rfl
        · rw [if_neg hEq]
          have ih' := ih (j := j + 1) hm'
          constructor
          · intro h
            rcases (ih'.1 h) with ⟨k, hj1k, hk, hxk⟩
            exact ⟨k, le_trans (Nat.le_succ j) hj1k, hk, hxk⟩
          · rintro ⟨k, hjk, hk, hxk⟩
            have hcases : j < k ∨ j = k := Nat.lt_or_eq_of_le hjk
            cases hcases with
            | inl hjlt =>
                have hj1k : j + 1 ≤ k := (Nat.succ_le_iff).2 hjlt
                exact (ih'.2 ⟨k, hj1k, hk, hxk⟩)
            | inr hjeq =>
                have : xi = nums[j]! := by simpa [hjeq] using hxk
                exact (hEq this).elim

  have outer_spec :
      ∀ (i : Nat),
        implementation.outer nums i = true ↔
          ∃ a b, i ≤ a ∧ a < b ∧ b < nums.size ∧ nums[a]! = nums[b]! := by
    intro i
    generalize hm : nums.size - i = m
    induction m generalizing i with
    | zero =>
        have hle : nums.size ≤ i := by
          by_contra hlt
          have hi : i < nums.size := Nat.lt_of_not_ge hlt
          have hpos : 0 < nums.size - i := Nat.sub_pos_of_lt hi
          simpa [hm] using hpos
        have hiFalse : ¬ i < nums.size := Nat.not_lt_of_ge hle
        unfold implementation.outer
        rw [dif_neg hiFalse]
        constructor
        · intro h
          simpa using h
        · rintro ⟨a, b, hia, hab, hb, _⟩
          have haSize : a < nums.size := lt_of_lt_of_le hab (Nat.le_of_lt hb)
          have hi : i < nums.size := lt_of_le_of_lt hia haSize
          exact (hiFalse hi).elim

    | succ m ih =>
        have hi : i < nums.size := by
          by_contra hni
          have hle : nums.size ≤ i := Nat.le_of_not_gt hni
          have hsub : nums.size - i = 0 := Nat.sub_eq_zero_of_le hle
          have : m.succ = 0 := by simpa [hm] using hsub
          exact (Nat.succ_ne_zero m) this

        have hm' : nums.size - (i + 1) = m := by
          simpa [Nat.sub_succ, hm, Nat.succ_sub_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

        have ih' := ih (i := i + 1) hm'

        unfold implementation.outer
        rw [dif_pos hi]
        -- Now: if inner(i+1) then true else outer(i+1)
        -- (note: condition is a Prop: inner(i+1) = true)
        by_cases hInner : implementation.outer.inner nums nums[i]! (i + 1) = true
        · -- inner found a duplicate at i
          -- simplify the boolean equation
          have hL : (if implementation.outer.inner nums nums[i]! (i + 1) = true then true else implementation.outer nums (i + 1)) = true := by
            simp [hInner]
          constructor
          · intro _
            -- produce witness from inner_spec
            rcases (inner_spec (xi := nums[i]!) (j := i + 1)).1 hInner with ⟨b, hi1b, hb, hEq⟩
            have hib : i < b := (Nat.succ_le_iff).1 hi1b
            exact ⟨i, b, le_rfl, hib, hb, by simpa using hEq⟩
          · intro _
            exact hL
        · -- inner did not find; use recursion
          have hL : (if implementation.outer.inner nums nums[i]! (i + 1) = true then true else implementation.outer nums (i + 1)) = true ↔
              implementation.outer nums (i + 1) = true := by
            simp [hInner]
          constructor
          · intro h
            have hOuter : implementation.outer nums (i + 1) = true := (hL.1 h)
            rcases (ih'.1 hOuter) with ⟨a, b, hia, hab, hb, hEq⟩
            exact ⟨a, b, le_trans (Nat.le_succ i) hia, hab, hb, hEq⟩
          · rintro ⟨a, b, hia, hab, hb, hEq⟩
            have hcase : a = i ∨ i < a := by
              have := Nat.lt_or_eq_of_le hia
              cases this with
              | inl hlt => exact Or.inr hlt
              | inr heq => exact Or.inl heq.symm
            cases hcase with
            | inl hae =>
                -- contradict hInner: if a=i then inner must be true
                have hi1b : i + 1 ≤ b := (Nat.succ_le_iff).2 (by simpa [hae] using hab)
                have : implementation.outer.inner nums nums[i]! (i + 1) = true :=
                  (inner_spec (xi := nums[i]!) (j := i + 1)).2 ⟨b, hi1b, hb, by simpa [hae] using hEq⟩
                exact (hInner this).elim
            | inr hilt =>
                have hi1a : i + 1 ≤ a := (Nat.succ_le_iff).2 hilt
                have hOuter : implementation.outer nums (i + 1) = true :=
                  (ih'.2 ⟨a, b, hi1a, hab, hb, hEq⟩)
                exact hL.2 hOuter

  simpa [HasDuplicate] using (outer_spec 0)



theorem correctness_goal_1
    (nums : Array ℤ)
    (h_precond : precondition nums)
    : implementation.outer nums 0 = false ↔ ¬HasDuplicate nums := by
  -- precondition is `True`, so we ignore `h_precond`
  have h0 : implementation.outer nums 0 = true ↔ HasDuplicate nums := by
    simpa using (correctness_goal_0 (nums := nums))
  constructor
  · intro hout_false
    intro hdup
    have hout_true : implementation.outer nums 0 = true := h0.mpr hdup
    have : (false : Bool) = true := by
      simpa [hout_false] using hout_true
    exact Bool.false_ne_true this
  · intro hnodup
    -- case split on the result boolean
    cases h : implementation.outer nums 0 with
    | false =>
        -- goal is exactly `h`
        simpa using h
    | true =>
        have hdup : HasDuplicate nums := h0.mp h
        have : False := hnodup hdup
        exact False.elim this

theorem correctness_goal
    (nums : Array Int)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical
  unfold postcondition
  constructor
  · unfold implementation
    -- what is outer?
    -- we prove main equivalence as separate lemma
    have htrue : implementation.outer nums 0 = true ↔ HasDuplicate nums := by
      expose_names; exact (correctness_goal_0 nums)
    simpa [HasDuplicate] using htrue
  · unfold implementation
    have hfalse : implementation.outer nums 0 = false ↔ ¬ HasDuplicate nums := by
      expose_names; exact (correctness_goal_1 nums h_precond)
    simpa using hfalse
end Proof
