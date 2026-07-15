import Lean
import Mathlib.Tactic
import Velvet.Std

set_option maxHeartbeats 10000000

section Specs
-- Never add new imports here

set_option maxHeartbeats 10000000
set_option pp.coercions false

/- Problem Description
    645. Set Mismatch: identify the duplicated number and the missing number in an array that should represent {1..n}.
    **Important: complexity should be O(n ^ 2) time and O(n) space**
    Natural language breakdown:
    1. The input is an array `nums` of length `n`.
    2. The intended correct set of values is exactly the integers from 1 to n (each appearing once).
    3. Due to an error, exactly one value in 1..n appears twice in `nums` (the duplicated value).
    4. As a consequence, exactly one value in 1..n appears zero times in `nums` (the missing value).
    5. Every element of `nums` is in the range 1..n.
    6. The output is an array of length 2: [duplicated, missing].
    7. The duplicated value must occur exactly twice in `nums`.
    8. The missing value must occur exactly zero times in `nums`.
    9. Every other value in 1..n must occur exactly once in `nums`.
-/

-- Helper: membership in the intended domain {1,2,...,n}
def inOneToN (n : Nat) (x : Nat) : Prop :=
  1 ≤ x ∧ x ≤ n

-- Helper: the core characterization of a valid set-mismatch instance
-- (there exists exactly one duplicated value and one missing value).
def hasSetMismatch (nums : Array Nat) : Prop :=
  let n : Nat := nums.size
  (n > 0) ∧
  (∀ (i : Nat), i < n → inOneToN n nums[i]!) ∧
  (∃ (dup : Nat) (miss : Nat),
      dup ≠ miss ∧
      inOneToN n dup ∧
      inOneToN n miss ∧
      nums.count dup = 2 ∧
      nums.count miss = 0 ∧
      (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1))

-- Preconditions
-- We require exactly the set-mismatch structure described above.
def precondition (nums : Array Nat) : Prop :=
  hasSetMismatch nums

-- Postconditions
-- The result is an array [dup, miss] that matches the unique count-pattern.
def postcondition (nums : Array Nat) (result : Array Nat) : Prop :=
  let n : Nat := nums.size
  result.size = 2 ∧
  let dup : Nat := result[0]!
  let miss : Nat := result[1]!
  dup ≠ miss ∧
  inOneToN n dup ∧
  inOneToN n miss ∧
  nums.count dup = 2 ∧
  nums.count miss = 0 ∧
  (∀ (x : Nat), inOneToN n x → x ≠ dup → x ≠ miss → nums.count x = 1)
end Specs

section Impl
def implementation (nums : Array Nat) : Array Nat :=
  let n := nums.size
  -- Brute-force counts (O(n^2) time), with only O(1) extra state.
  let rec go (x : Nat) (dup miss : Nat) : Nat × Nat :=
    if hx : x ≤ n then
      let c := nums.count x
      let dup' := if c = 2 then x else dup
      let miss' := if c = 0 then x else miss
      go (x + 1) dup' miss'
    else
      (dup, miss)
    termination_by (n + 1) - x
  let dm := go 1 0 0
  #[dm.1, dm.2]
end Impl

section TestCases
-- Test case 1: Example 1
def test1_nums : Array Nat := #[1, 2, 2, 4]
def test1_Expected : Array Nat := #[2, 3]

-- Test case 2: Example 2
def test2_nums : Array Nat := #[1, 1]
def test2_Expected : Array Nat := #[1, 2]

-- Test case 3: duplicate is the maximum, missing is the minimum
def test3_nums : Array Nat := #[2, 2]
def test3_Expected : Array Nat := #[2, 1]

-- Test case 4: n = 3, missing is the maximum
def test4_nums : Array Nat := #[1, 2, 2]
def test4_Expected : Array Nat := #[2, 3]

-- Test case 5: n = 3, duplicate appears at both ends
def test5_nums : Array Nat := #[3, 1, 3]
def test5_Expected : Array Nat := #[3, 2]

-- Test case 6: n = 4, duplicate in the middle, missing at the end
def test6_nums : Array Nat := #[1, 2, 3, 3]
def test6_Expected : Array Nat := #[3, 4]

-- Test case 7: n = 5, unsorted, duplicate is small, missing is maximum
def test7_nums : Array Nat := #[2, 1, 1, 4, 3]
def test7_Expected : Array Nat := #[1, 5]

-- Test case 8: n = 6, duplicate is interior, missing is interior
def test8_nums : Array Nat := #[1, 5, 3, 4, 2, 2]
def test8_Expected : Array Nat := #[2, 6]

-- Test case 9: n = 7, larger case, duplicate is maximum, missing is interior
def test9_nums : Array Nat := #[1, 2, 3, 4, 5, 7, 7]
def test9_Expected : Array Nat := #[7, 6]
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
theorem correctness_goal
    (nums : Array Nat)
    (h_precond : precondition nums)
    : postcondition nums (implementation nums) := by
  classical
  simp [precondition, hasSetMismatch] at h_precond
  rcases h_precond with ⟨hnpos, hdom, h⟩
  rcases h with ⟨dup, miss, hne, hdupIn, hmissIn, hcountDup, hcountMiss, hcountOther⟩

  have go_unfold (x d m : Nat) :
      implementation.go nums nums.size x d m =
        (if hx : x ≤ nums.size then
          let c := nums.count x
          let d' := if c = 2 then x else d
          let m' := if c = 0 then x else m
          implementation.go nums nums.size (x + 1) d' m'
        else
          (d, m)) := by
    conv_lhs =>
      unfold implementation.go

  have if_lt_succ (a k : Nat) (h : a ≠ k) :
      (if a < k then a else 0) = (if a < k + 1 then a else 0) := by
    cases lt_or_gt_of_ne h with
    | inl hak =>
        have hak' : a < k + 1 := Nat.lt_trans hak (Nat.lt_succ_self k)
        simp [hak, hak']
    | inr hka =>
        have hnot1 : ¬ a < k := not_lt_of_ge (Nat.le_of_lt hka)
        have hnot2 : ¬ a < k + 1 := not_lt_of_ge (Nat.succ_le_of_lt hka)
        simp [hnot1, hnot2]

  have go_correct :
      ∀ x : Nat,
        1 ≤ x →
          implementation.go nums nums.size x (if dup < x then dup else 0)
              (if miss < x then miss else 0) = (dup, miss) := by
    intro x hx1
    have hxP :
        (1 ≤ x →
            implementation.go nums nums.size x (if dup < x then dup else 0)
                (if miss < x then miss else 0) = (dup, miss)) := by
      refine
        Nat.strong_decreasing_induction
          (P := fun x =>
            1 ≤ x →
              implementation.go nums nums.size x (if dup < x then dup else 0)
                  (if miss < x then miss else 0) = (dup, miss))
          ?base ?step x
      · refine ⟨nums.size, ?_⟩
        intro m hmgt hm1
        have hxnle : ¬ m ≤ nums.size := not_le_of_gt hmgt
        have hdup_lt_m : dup < m := Nat.lt_of_le_of_lt hdupIn.2 hmgt
        have hmiss_lt_m : miss < m := Nat.lt_of_le_of_lt hmissIn.2 hmgt
        rw [go_unfold (x := m) (d := if dup < m then dup else 0) (m := if miss < m then miss else 0)]
        simp [hxnle, hdup_lt_m, hmiss_lt_m]
      · intro k ih hk1
        by_cases hk_le : k ≤ nums.size
        · rw [go_unfold (x := k) (d := if dup < k then dup else 0) (m := if miss < k then miss else 0)]
          simp [hk_le]
          have hk1' : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
          have ih_succ := ih (k + 1) (Nat.lt_succ_self k) hk1'

          have hd :
              (if nums.count k = 2 then k else (if dup < k then dup else 0)) =
                (if dup < k + 1 then dup else 0) := by
            by_cases hkdup : k = dup
            · rw [hkdup]
              have hdup_lt : dup < dup + 1 := Nat.lt_succ_self dup
              simp [hcountDup, hdup_lt]
            · have hk_count_ne2 : nums.count k ≠ 2 := by
                by_cases hkmiss : k = miss
                · have : nums.count k = 0 := by simpa [hkmiss] using hcountMiss
                  simpa [this]
                · have hk_in : inOneToN nums.size k := ⟨hk1, hk_le⟩
                  have : nums.count k = 1 := hcountOther k hk_in hkdup hkmiss
                  simpa [this]
              have := if_lt_succ dup k (Ne.symm hkdup)
              simpa [hk_count_ne2] using this

          have hm :
              (if nums.count k = 0 then k else (if miss < k then miss else 0)) =
                (if miss < k + 1 then miss else 0) := by
            by_cases hkmiss : k = miss
            · rw [hkmiss]
              have hmiss_lt : miss < miss + 1 := Nat.lt_succ_self miss
              simp [hcountMiss, hmiss_lt]
            · have hk_count_ne0 : nums.count k ≠ 0 := by
                by_cases hkdup : k = dup
                · have : nums.count k = 2 := by simpa [hkdup] using hcountDup
                  simpa [this]
                · have hk_in : inOneToN nums.size k := ⟨hk1, hk_le⟩
                  have : nums.count k = 1 := hcountOther k hk_in hkdup hkmiss
                  simpa [this]
              have := if_lt_succ miss k (Ne.symm hkmiss)
              simpa [hk_count_ne0] using this

          simpa [hd, hm] using ih_succ
        · have hkgt : nums.size < k := Nat.lt_of_not_ge hk_le
          have hxnle : ¬ k ≤ nums.size := not_le_of_gt hkgt
          have hdup_lt_k : dup < k := Nat.lt_of_le_of_lt hdupIn.2 hkgt
          have hmiss_lt_k : miss < k := Nat.lt_of_le_of_lt hmissIn.2 hkgt
          rw [go_unfold (x := k) (d := if dup < k then dup else 0) (m := if miss < k then miss else 0)]
          simp [hxnle, hdup_lt_k, hmiss_lt_k]
    exact hxP hx1

  have hdup_not_lt1 : ¬ dup < 1 := not_lt_of_ge hdupIn.1
  have hmiss_not_lt1 : ¬ miss < 1 := not_lt_of_ge hmissIn.1
  have hgo : implementation.go nums nums.size 1 0 0 = (dup, miss) := by
    have h := go_correct 1 (by simp)
    simpa [hdup_not_lt1, hmiss_not_lt1] using h

  simp [postcondition, implementation, hgo]
  exact ⟨hne, hdupIn, hmissIn, hcountDup, hcountMiss, hcountOther⟩
end Proof
